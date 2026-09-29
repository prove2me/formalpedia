-- Prove2me | solution 1 for exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/f25566b1-b351-5df4-b98e-605c9e7e13e2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField

set_option autoImplicit false

open scoped TensorProduct

namespace C2idemCore

namespace IdempotentOrbit

section Ind

variable {ι : Type*} [DecidableEq ι] {F : ι → Type*} [∀ i, Field (F i)]

def ind (S : Finset ι) : (Π i, F i) := fun i => if i ∈ S then 1 else 0

theorem ind_apply (S : Finset ι) (i : ι) : (ind S : Π i, F i) i = if i ∈ S then 1 else 0 := rfl

theorem ind_mul (S T : Finset ι) : (ind S : Π i, F i) * ind T = ind (S ∩ T) := by
  ext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [ind, hS, hT]

theorem isIdempotentElem_ind (S : Finset ι) : IsIdempotentElem (ind S : Π i, F i) := by
  show ind S * ind S = ind S
  rw [ind_mul, Finset.inter_self]

theorem ind_empty : (ind (∅ : Finset ι) : Π i, F i) = 0 := by
  ext i; simp [ind]

theorem ind_univ [Fintype ι] : (ind (Finset.univ : Finset ι) : Π i, F i) = 1 := by
  ext i; simp [ind]

theorem ind_injective : Function.Injective (ind (F := F)) := by
  intro S T h
  ext i
  have hi := congr_fun h i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all [ind]

theorem ind_eq_sum (S : Finset ι) : (ind S : Π i, F i) = ∑ k ∈ S, ind {k} := by
  ext i
  simp only [Finset.sum_apply, ind_apply, Finset.mem_singleton]
  rw [Finset.sum_ite_eq]

theorem ind_singleton_mul_ind_singleton {a b : ι} (h : a ≠ b) :
    (ind {a} : Π i, F i) * ind {b} = 0 := by
  ext j
  by_cases ha : j = a
  · subst ha; simp [ind, h]
  · simp [ind, ha]

theorem existsUnique_map_ind_singleton_eq_one [Fintype ι] {D : Type*} [Field D]
    (g : (Π i, F i) →+* D) : ∃! k, g (ind {k}) = 1 := by
  have h01 : ∀ k, g (ind {k}) = 0 ∨ g (ind {k}) = 1 := fun k =>
    IsIdempotentElem.iff_eq_zero_or_one.mp ((isIdempotentElem_ind {k}).map g)
  have hsum : ∑ k, g (ind {k}) = 1 := by
    rw [← map_sum, ← ind_eq_sum, ind_univ, map_one]
  obtain ⟨k, -, hk⟩ : ∃ k ∈ (Finset.univ : Finset ι), g (ind {k}) ≠ 0 :=
    Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  refine ⟨k, (h01 k).resolve_left hk, fun k' hk' => ?_⟩
  by_contra hne
  have h0 : g (ind {k'}) * g (ind {k}) = 0 := by
    rw [← map_mul, ind_singleton_mul_ind_singleton hne, map_zero]
  rw [hk', (h01 k).resolve_left hk, one_mul] at h0
  exact one_ne_zero h0

variable [Fintype ι]

noncomputable def kappa (t : (Π i, F i) →+* Π i, F i) (i : ι) : ι :=
  Classical.choose (existsUnique_map_ind_singleton_eq_one ((Pi.evalRingHom F i).comp t)).exists

theorem apply_ind_singleton_apply (t : (Π i, F i) →+* Π i, F i) (k i : ι) :
    t (ind {k}) i = if kappa t i = k then 1 else 0 := by
  have hu := existsUnique_map_ind_singleton_eq_one ((Pi.evalRingHom F i).comp t)
  have hspec : t (ind {kappa t i}) i = 1 := Classical.choose_spec hu.exists
  split_ifs with h
  · subst h; exact hspec
  · have h01 : t (ind {k}) i = 0 ∨ t (ind {k}) i = 1 :=
      IsIdempotentElem.iff_eq_zero_or_one.mp
        (((isIdempotentElem_ind {k}).map t).map (Pi.evalRingHom F i))
    rcases h01 with h0 | h1
    · exact h0
    · exact absurd (hu.unique h1 hspec).symm h

theorem apply_ind (t : (Π i, F i) →+* Π i, F i) (S : Finset ι) :
    t (ind S) = ind (Finset.univ.filter fun i => kappa t i ∈ S) := by
  ext i
  rw [ind_eq_sum S, map_sum, Finset.sum_apply]
  simp only [apply_ind_singleton_apply, ind_apply, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [Finset.sum_ite_eq]

theorem exists_indexMap_of_iterate_eq (t : (Π i, F i) →+* Π i, F i) {n : ℕ} (hn : 0 < n)
    (htn : ∀ x, (⇑t)^[n] x = x) :
    ∃ ψ : ι → ι, (∀ m j, (⇑t)^[m] (ind {j}) = ind {ψ^[m] j}) ∧ (∀ i, ψ^[n] i = i) ∧
      (∀ S : Finset ι, (∀ i, ψ i ∈ S ↔ i ∈ S) → t (ind S) = ind S) := by
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩

  have hiter : ∀ (m : ℕ) (S : Finset ι),
      (⇑t)^[m] (ind S) = ind (Finset.univ.filter fun i => (kappa t)^[m] i ∈ S) := by
    intro m
    induction m with
    | zero => intro S; simp
    | succ m ih =>
      intro S
      rw [Function.iterate_succ_apply, apply_ind, ih]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← Function.iterate_succ_apply' (kappa t) m i, Function.iterate_succ_apply]

  have hκn : ∀ i, (kappa t)^[n] i = i := by
    intro i
    have h := hiter n {(kappa t)^[n] i}
    rw [htn] at h
    have h' := ind_injective h
    have hi : i ∈ Finset.univ.filter fun j => (kappa t)^[n] j ∈ ({(kappa t)^[n] i} : Finset ι) := by simp
    rw [← h'] at hi
    exact (Finset.mem_singleton.mp hi).symm
  refine ⟨(kappa t)^[n'], ?_, ?_, ?_⟩
  ·
    have hκψ : ∀ i, kappa t ((kappa t)^[n'] i) = i := fun i => by
      have := hκn i; rwa [hn', Function.iterate_succ_apply'] at this
    have hψκ : ∀ i, (kappa t)^[n'] (kappa t i) = i := fun i => by
      have := hκn i; rwa [hn', Function.iterate_succ_apply] at this
    have h1 : ∀ j, t (ind {j}) = ind {(kappa t)^[n'] j} := fun j => by
      rw [apply_ind]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; rw [← h, hψκ]
      · intro h; rw [h, hκψ]
    intro m
    induction m with
    | zero => intro j; rfl
    | succ m ih =>
      intro j
      rw [Function.iterate_succ_apply, h1, ih, ← Function.iterate_succ_apply]
  · intro i
    rw [← Function.iterate_mul, mul_comm, Function.iterate_mul]
    exact Function.iterate_fixed (hκn i) _
  · intro S hS
    have hκψ : ∀ i, kappa t ((kappa t)^[n'] i) = i := fun i => by
      have := hκn i; rwa [hn', Function.iterate_succ_apply'] at this
    rw [apply_ind]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

    have := hS (kappa t i)
    rw [show ((kappa t)^[n']) (kappa t i) = i from by
      have := hκn i; rwa [hn', Function.iterate_succ_apply] at this] at this
    exact this.symm

end Ind

section Core

variable {R : Type*} [CommRing R] {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]

def conj (φ : R ≃+* Π i, F i) (s : R →+* R) : (Π i, F i) →+* Π i, F i :=
  φ.toRingHom.comp (s.comp φ.symm.toRingHom)

theorem conj_apply (φ : R ≃+* Π i, F i) (s : R →+* R) (x : Π i, F i) :
    conj φ s x = φ (s (φ.symm x)) := rfl

theorem semiconj_conj (φ : R ≃+* Π i, F i) (s : R →+* R) :
    Function.Semiconj φ s (conj φ s) := fun a => by
  rw [conj_apply, RingEquiv.symm_apply_apply]

theorem exists_idempotent_orbit_or_isField [Finite ι] (φ : R ≃+* Π i, F i) (s : R →+* R)
    {n : ℕ} (hn : n.Prime) (hs : ∀ a, (⇑s)^[n] a = a)
    {k : Type*} [Field k] (f : k →+* R) (hfix : ∀ a, s a = a → a ∈ Set.range f) :
    (∃ e : R, IsIdempotentElem e ∧ (∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) ∧
        (∑ i ∈ Finset.range n, (⇑s)^[i] e) = 1) ∨ IsField R := by
  classical
  letI := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨j₀⟩⟩
  ·
    haveI : Subsingleton R := φ.toEquiv.subsingleton
    exact Or.inl ⟨0, Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  haveI : Nontrivial R := ⟨⟨φ.symm 0, φ.symm 1, fun h => by
    have := congr_fun (φ.symm.injective h) j₀; simp at this⟩⟩

  have hfix01 : ∀ a : R, IsIdempotentElem a → s a = a → a = 0 ∨ a = 1 := by
    intro a ha hsa
    obtain ⟨x, rfl⟩ := hfix a hsa
    have hx : IsIdempotentElem x := by
      apply f.injective
      rw [map_mul]; exact ha
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hx with h | h
    · exact Or.inl (by rw [h, map_zero])
    · exact Or.inr (by rw [h, map_one])

  have htn : ∀ x, (⇑(conj φ s))^[n] x = x := fun x => by
    have := (semiconj_conj φ s).iterate_right n (φ.symm x)
    rw [hs, RingEquiv.apply_symm_apply] at this
    exact this.symm
  obtain ⟨ψ, hψm, hψn, hψS⟩ := exists_indexMap_of_iterate_eq (conj φ s) hn.pos htn
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := hn.pos; omega⟩

  have hinv : ∀ S : Finset ι, (∀ i, ψ i ∈ S ↔ i ∈ S) → S = ∅ ∨ S = Finset.univ := by
    intro S hS
    have hfixS := hψS S hS
    have ha : s (φ.symm (ind S)) = φ.symm (ind S) := by
      apply φ.injective
      rw [← conj_apply, hfixS, RingEquiv.apply_symm_apply]
    rcases hfix01 _ ((isIdempotentElem_ind S).map φ.symm) ha with h0 | h1
    · left
      apply ind_injective (F := F)
      have := congrArg φ h0
      rwa [RingEquiv.apply_symm_apply, map_zero, ← ind_empty] at this
    · right
      apply ind_injective (F := F)
      have := congrArg φ h1
      rwa [RingEquiv.apply_symm_apply, map_one, ← ind_univ] at this

  set S : Finset ι := (Finset.range n).image fun m => ψ^[m] j₀ with hSdef
  have hmemS : ∀ m, ψ^[m] j₀ ∈ S := by
    intro m
    rw [hSdef, Finset.mem_image]
    refine ⟨m % n, Finset.mem_range.mpr (Nat.mod_lt m hn.pos), ?_⟩
    conv_rhs => rw [← Nat.mod_add_div m n, Function.iterate_add_apply, Function.iterate_mul]
    rw [Function.iterate_fixed (hψn j₀)]
  have hSinv : ∀ i, ψ i ∈ S ↔ i ∈ S := by
    intro i
    constructor
    · intro h
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp h
      have : i = ψ^[n' + m] j₀ := by
        rw [Function.iterate_add_apply, hm]
        have h2 := hψn i
        rw [hn', Function.iterate_succ_apply] at h2
        exact h2.symm
      rw [this]; exact hmemS _
    · intro h
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp h
      rw [← hm, ← Function.iterate_succ_apply' ψ m j₀]
      exact hmemS _
  have hSuniv : S = Finset.univ :=
    (hinv S hSinv).resolve_left (Finset.nonempty_iff_ne_empty.mp ⟨j₀, hmemS 0⟩)
  by_cases hfixpt : ψ j₀ = j₀
  ·
    right
    have hall : ∀ i : ι, i = j₀ := by
      intro i
      have hi : i ∈ S := hSuniv ▸ Finset.mem_univ i
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hi
      rw [← hm]; exact Function.iterate_fixed hfixpt m
    letI : Unique ι := ⟨⟨j₀⟩, hall⟩
    exact MulEquiv.isField (Field.toIsField (F default))
      (φ.trans (RingEquiv.piUnique F)).toMulEquiv
  ·
    left
    have hper : Function.minimalPeriod ψ j₀ = n := by
      have hdvd : Function.minimalPeriod ψ j₀ ∣ n :=
        Function.IsPeriodicPt.minimalPeriod_dvd (hψn j₀)
      rcases (Nat.dvd_prime hn).mp hdvd with h1 | h2
      · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1) hfixpt
      · exact h2
    have hinj : Set.InjOn (fun m => ψ^[m] j₀) (Set.Iio n) :=
      hper ▸ Function.iterate_injOn_Iio_minimalPeriod
    have hne : ∀ i, 0 < i → i < n → j₀ ≠ ψ^[i] j₀ := by
      intro i hi0 hin h
      have : (0 : ℕ) = i := hinj (Set.mem_Iio.mpr hn.pos) (Set.mem_Iio.mpr hin) h
      omega
    refine ⟨φ.symm (ind {j₀}), (isIdempotentElem_ind {j₀}).map φ.symm, ?_, ?_⟩
    · intro i hi0 hin
      apply φ.injective
      rw [map_mul, map_zero, (semiconj_conj φ s).iterate_right i, RingEquiv.apply_symm_apply, hψm,
        ind_singleton_mul_ind_singleton (hne i hi0 hin)]
    · apply φ.injective
      rw [map_sum, map_one]
      simp_rw [(semiconj_conj φ s).iterate_right _ _, RingEquiv.apply_symm_apply, hψm]
      rw [← Finset.sum_image (f := fun k => (ind {k} : Π i, F i))
        (fun a ha b hb h => hinj (by simpa using ha) (by simpa using hb) h)]
      rw [← hSdef, hSuniv, ← ind_eq_sum, ind_univ]

end Core

end IdempotentOrbit

end C2idemCore

namespace SplitOrbit

theorem main (F A : Type) [Field F] [CommRing A] [Algebra F A] [Module.Finite F A] [IsReduced A]
    (s : A →+* A) (n : ℕ) (hn : n.Prime) (hsn : (⇑s)^[n] = id)
    (hfix : ∀ a : A, s a = a → a ∈ Set.range (algebraMap F A))
    (hA : ¬ IsField A) :
    ∃ e : A, IsIdempotentElem e ∧ (∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) ∧
      (∑ i ∈ Finset.range n, (⇑s)^[i] e) = 1 := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  letI : ∀ I : MaximalSpectrum A, Field (A ⧸ I.asIdeal) := fun I => Ideal.Quotient.field I.asIdeal
  have h := C2idemCore.IdempotentOrbit.exists_idempotent_orbit_or_isField
    (IsArtinianRing.equivPi A).toRingEquiv s hn (fun a => congr_fun hsn a) (algebraMap F A) hfix
  exact h.resolve_right hA

end SplitOrbit

theorem solution
    (F A : Type) [Field F] [CommRing A] [Algebra F A] [Module.Finite F A] [IsReduced A]
    (s : A →+* A) (n : ℕ) (hn : n.Prime) (hsn : (⇑s)^[n] = id)
    (hfix : ∀ a : A, s a = a → a ∈ Set.range (algebraMap F A))
    (hA : ¬ IsField A) :
    ∃ e : A, IsIdempotentElem e ∧ (∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) ∧
      (∑ i ∈ Finset.range n, (⇑s)^[i] e) = 1 :=
  SplitOrbit.main F A s n hn hsn hfix hA

end S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField
end P2MW
export P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField (solution)
