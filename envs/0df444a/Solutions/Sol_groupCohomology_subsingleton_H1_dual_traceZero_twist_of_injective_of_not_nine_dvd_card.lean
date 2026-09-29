-- Prove2me | solution 1 for groupCohomology.subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/b379d082-f0f3-5588-8304-60263565504d

import Mathlib
import Theorems.Thm_groupCohomology_subsingleton_H1_of_isUnit_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card

set_option autoImplicit false

open groupCohomology Matrix

namespace P2mSyl3

section Generic

variable {R G : Type} [CommRing R] [Group G]

lemma H1π_eq_zero_of_exists (A : Rep.{0} R G) (x : cocycles₁ A)
    (h : ∃ m : A, ∀ g : G, x g = A.ρ g m - m) : H1π A x = 0 := by
  rw [H1π_eq_zero_iff]
  obtain ⟨m, hm⟩ := h
  refine ⟨m, ?_⟩
  funext g
  rw [hm g]
  rfl

lemma subsingleton_H1_of_forall (A : Rep.{0} R G)
    (h : ∀ x : cocycles₁ A, ∃ m : A, ∀ g : G, x g = A.ρ g m - m) : Subsingleton (H1 A) := by
  constructor
  intro a b
  revert b
  refine H1_induction_on a fun x => ?_
  intro b
  refine H1_induction_on b fun y => ?_
  rw [H1π_eq_zero_of_exists A x (h x), H1π_eq_zero_of_exists A y (h y)]

lemma exists_of_exists_subgroup (A : Rep.{0} R G) (P : Subgroup G) [P.FiniteIndex]
    (hunit : IsUnit ((P.index : ℕ) : R)) (x : cocycles₁ A) (m : A)
    (hm : ∀ p ∈ P, x p = A.ρ p m - m) : ∃ m' : A, ∀ g : G, x g = A.ρ g m' - m' := by
  classical

  set x' : G → A := fun g => x g - (A.ρ g m - m) with hx'
  have hxcoc := (mem_cocycles₁_iff x).1 x.2
  have hx'coc : ∀ g h : G, x' (g * h) = A.ρ g (x' h) + x' g := by
    intro g h
    simp only [hx', hxcoc, map_mul, Module.End.mul_apply, map_sub]
    abel
  have hx'P : ∀ p ∈ P, x' p = 0 := by
    intro p hp; simp only [hx', hm p hp, sub_self]
  have hx'const : ∀ (g : G), ∀ p ∈ P, x' (g * p) = x' g := by
    intro g p hp
    rw [hx'coc, hx'P p hp, map_zero, zero_add]
  haveI : Fintype (G ⧸ P) := Fintype.ofFinite _
  set S : A := ∑ C : G ⧸ P, x' C.out with hS
  have hout : ∀ g : G, x' ((g : G ⧸ P).out) = x' g := by
    intro g
    obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul P g
    rw [hp, hx'const g p p.2]
  have hSh : ∀ h : G, A.ρ h S = S - ((P.index : ℕ) : R) • x' h := by
    intro h
    have h1 : ∀ C : G ⧸ P, A.ρ h (x' C.out) = x' ((h • C).out) - x' h := by
      intro C
      have := hx'coc h C.out
      rw [eq_sub_iff_add_eq, ← this, ← hout (h * C.out)]
      congr 2
      rw [← MulAction.Quotient.coe_smul_out, smul_eq_mul]
    rw [hS, map_sum, Finset.sum_congr rfl fun C _ => h1 C, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, Nat.cast_smul_eq_nsmul]
    congr 1
    exact Fintype.sum_equiv (MulAction.toPerm h) _ _ fun C => rfl
  obtain ⟨r, hr⟩ := hunit.exists_left_inv
  refine ⟨m - r • S, fun g => ?_⟩
  have hg : x g = x' g + (A.ρ g m - m) := by simp only [hx', sub_add_cancel]
  rw [hg, map_sub, map_smul, hSh g, smul_sub, smul_smul, hr, one_smul]
  abel

end Generic

section Cyclic

variable {G : Type} [Group G]

lemma eq_on_zpowers (A : Rep.{0} (ZMod 3) G) (x : cocycles₁ A) (u : G) (hu : IsOfFinOrder u) (m : A)
    (hm : x u = A.ρ u m - m) : ∀ p ∈ Subgroup.zpowers u, x p = A.ρ p m - m := by
  intro p hp
  rw [← hu.mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hp
  obtain ⟨i, rfl⟩ := hp
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, (mem_cocycles₁_iff x).1 x.2, ih, hm, map_sub, ← Module.End.mul_apply, ← map_mul,
      ← pow_succ]
    abel

lemma sq_sub_one_apply_eq_zero (A : Rep.{0} (ZMod 3) G) (x : cocycles₁ A) (u : G) (hu : u ^ 3 = 1) :
    (A.ρ u - 1) ((A.ρ u - 1) (x u)) = 0 := by
  have hcoc := (mem_cocycles₁_iff x).1 x.2
  have h2 : x (u ^ 2) = A.ρ u (x u) + x u := by rw [sq, hcoc]
  have h3 : x (u ^ 3) = A.ρ u (A.ρ u (x u)) + A.ρ u (x u) + x u := by
    rw [pow_succ', hcoc, h2, map_add]
  rw [hu, cocycles₁_map_one] at h3
  have h3' : (3 : ZMod 3) • A.ρ u (x u) = 0 := by
    rw [show (3 : ZMod 3) = 0 from rfl, zero_smul]
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]

  have : A.ρ u (A.ρ u (x u)) - A.ρ u (x u) - (A.ρ u (x u) - x u) =
      (A.ρ u (A.ρ u (x u)) + A.ρ u (x u) + x u) - (3 : ZMod 3) • A.ρ u (x u) := by
    rw [show (3 : ZMod 3) • A.ρ u (x u) = A.ρ u (x u) + A.ρ u (x u) + A.ρ u (x u) by
      rw [show (3 : ZMod 3) = 1 + 1 + 1 from rfl, add_smul, add_smul, one_smul]]
    abel
  rw [this, ← h3, h3', sub_zero]

end Cyclic

section Duality

variable {K M : Type} [Field K] [AddCommGroup M] [Module K M]

lemma exists_dualMap_eq (D : M →ₗ[K] M) (hD : LinearMap.ker D ≤ LinearMap.range (D ∘ₗ D))
    (f : Module.Dual K M) (hf : D.dualMap (D.dualMap f) = 0) : ∃ g : Module.Dual K M, D.dualMap g = f := by
  have h1 : f ∈ LinearMap.ker (D ∘ₗ D).dualMap := by
    rw [LinearMap.mem_ker]
    ext v
    have := congrArg (fun φ : Module.Dual K M => φ v) hf
    simpa [LinearMap.dualMap_apply] using this
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range] at h1
  have h2 : f ∈ (LinearMap.ker D).dualAnnihilator := Submodule.dualAnnihilator_anti hD h1
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at h2
  exact h2

end Duality

section Jordan

variable {k : Type} [Field k] [CharP k 3] {V : Type} [AddCommGroup V] [Module k V]

lemma three_eq_zero : (3 : k) = 0 := by simpa using CharP.cast_eq_zero k 3

lemma two_ne_zero' : (2 : k) ≠ 0 := by
  have h3 : (3 : k) = 0 := three_eq_zero
  intro h2
  have : (1 : k) = 0 := by linear_combination h3 - h2
  exact one_ne_zero this

omit [CharP k 3] in

lemma exists_vec (n : Module.End k V) (hn : n ≠ 0) (hn3 : n ^ 3 = 0) :
    ∃ v : V, n v ≠ 0 ∧ n (n v) = 0 := by
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, n v₀ ≠ 0 := by
    by_contra! h
    exact hn (LinearMap.ext h)
  by_cases h2 : n (n v₀) = 0
  · exact ⟨v₀, hv₀, h2⟩
  · refine ⟨n v₀, h2, ?_⟩
    have := LinearMap.congr_fun hn3 v₀
    simpa [pow_succ] using this

lemma jordan (hV : Module.finrank k V = 2) (w w' : Module.End k V) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hww' : w * w' = 1) (X : Module.End k V) (hX : LinearMap.trace k V X = 0)
    (hfix : w * X * w' = X) :
    ∃ Y : Module.End k V, LinearMap.trace k V Y = 0 ∧
      w * (w * Y * w' - Y) * w' - (w * Y * w' - Y) = X := by
  classical

  set n : Module.End k V := w - 1 with hn
  have hn0 : n ≠ 0 := sub_ne_zero.2 hw1
  have h3E : (3 : Module.End k V) = 0 := by
    ext v
    change ((3 : ℕ) : Module.End k V) v = 0
    rw [Module.End.natCast_apply, ← Nat.cast_smul_eq_nsmul k, Nat.cast_ofNat, three_eq_zero, zero_smul]
  have hn3 : n ^ 3 = 0 := by
    have : (w - 1) ^ 3 = w ^ 3 - 3 * w ^ 2 + 3 * w - 1 := by noncomm_ring
    rw [hn, this, hw3, h3E, zero_mul, zero_mul, sub_zero, add_zero, sub_self]
  obtain ⟨v, hv1, hv2⟩ := exists_vec n hn0 hn3

  have hli : LinearIndependent k ![n v, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg n hst
    simp only [map_add, map_smul, hv2, smul_zero, zero_add, map_zero, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · subst h1
      simp only [zero_smul, add_zero, smul_eq_zero] at hst
      exact ⟨hst.resolve_right hv1, rfl⟩
    · exact absurd h1 hv1
  haveI : FiniteDimensional k V := Module.finite_of_finrank_pos (by omega)
  set b : Module.Basis (Fin 2) k V :=
    basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hV]) with hb
  have hb0 : b 0 = n v := by rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hb1 : b 1 = v := by rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]; rfl
  have hwb0 : w (b 0) = b 0 := by
    have : w = n + 1 := by rw [hn, sub_add_cancel]
    rw [this, hb0, LinearMap.add_apply, hv2, zero_add, Module.End.one_apply]
  have hwb1 : w (b 1) = b 0 + b 1 := by
    have : w = n + 1 := by rw [hn, sub_add_cancel]
    rw [this, hb1, hb0, LinearMap.add_apply, Module.End.one_apply]

  set W : Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrix b b w with hWdef
  have hW : W = !![1, 1; 0, 1] := by
    ext i j
    rw [hWdef, LinearMap.toMatrix_apply]
    fin_cases i <;> fin_cases j <;>
      simp [hwb0, hwb1]
  set W' : Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrix b b w' with hW'def
  have hWW' : W * W' = 1 := by
    rw [hWdef, hW'def, ← LinearMap.toMatrix_mul, hww', LinearMap.toMatrix_one]
  have hW' : W' = !![1, -1; 0, 1] := by
    have e1 : !![1, -1; 0, 1] * W = (1 : Matrix (Fin 2) (Fin 2) k) := by
      rw [hW]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    calc W' = (!![1, -1; 0, 1] * W) * W' := by rw [e1, one_mul]
      _ = !![1, -1; 0, 1] := by rw [mul_assoc, hWW', mul_one]
  set Xm : Matrix (Fin 2) (Fin 2) k := LinearMap.toMatrix b b X with hXmdef
  have htr : Xm 0 0 + Xm 1 1 = 0 := by
    rw [← Matrix.trace_fin_two, hXmdef, ← LinearMap.trace_eq_matrix_trace k b X, hX]
  have hfixm : W * Xm * W' = Xm := by
    rw [hWdef, hXmdef, hW'def, ← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul, hfix]

  have e00 := congrFun (congrFun hfixm 0) 0
  have e01 := congrFun (congrFun hfixm 0) 1
  simp only [hW, hW', Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  simp at e00 e01
  have h10 : Xm 1 0 = 0 := e00
  have h11 : Xm 1 1 = Xm 0 0 := by linear_combination e01 + e00
  have h00 : Xm 0 0 = 0 := by
    have : (2 : k) * Xm 0 0 = 0 := by linear_combination htr - h11
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero'
  have h11' : Xm 1 1 = 0 := by rw [h11, h00]
  have hXm : Xm = !![0, Xm 0 1; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h00, h10, h11']

  set Ym : Matrix (Fin 2) (Fin 2) k := !![0, 0; Xm 0 1, 0] with hYm
  refine ⟨(LinearMap.toMatrix b b).symm Ym, ?_, ?_⟩
  · rw [LinearMap.trace_eq_matrix_trace k b, LinearEquiv.apply_symm_apply, Matrix.trace_fin_two, hYm]
    simp
  · apply (LinearMap.toMatrix b b).injective
    have h3 : (3 : k) = 0 := three_eq_zero
    simp only [map_sub, LinearMap.toMatrix_mul, LinearEquiv.apply_symm_apply]
    rw [← hWdef, ← hW'def, ← hXmdef, hW, hW', hXm, hYm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring_nf
    first | rfl | linear_combination (Xm 0 1) * h3 | linear_combination (-(Xm 0 1)) * h3

end Jordan

section Main

variable {k : Type} [Field k] [CharP k 3]
  {V : Type} [AddCommGroup V] [Module k V]
  {Q : Type} [Group Q] [Finite Q]

lemma isUnit_natCast_of_not_dvd {n : ℕ} (h : ¬ 3 ∣ n) : IsUnit ((n : ℕ) : ZMod 3) :=
  (ZMod.isUnit_iff_coprime n 3).2
    (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h))

lemma units_eq_one_of_pow_three (x : (ZMod 3)ˣ) (hx : x ^ 3 = 1) : x = 1 := by
  have h2 : x ^ (3 - 1) = 1 := ZMod.units_pow_card_sub_one_eq_one 3 x
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [hx]; simpa using h2

theorem main (hV : Module.finrank k V = 2) (h9 : ¬ 9 ∣ Nat.card Q)
    (σ : Q →* Module.End k V) (hσ : Function.Injective σ)
    (χ : Q →* (ZMod 3)ˣ)
    [Module (ZMod 3) (LinearMap.ker (LinearMap.trace k V))]
    (A : Rep.{0} (ZMod 3) Q)
    (e : A ≃ₗ[ZMod 3] Module.Dual (ZMod 3) (LinearMap.ker (LinearMap.trace k V)))
    (he : ∀ (q : Q) (a : A) (X Y : LinearMap.ker (LinearMap.trace k V)),
      (Y : Module.End k V) = σ q⁻¹ * X * σ q → e (A.ρ q a) X = (χ q : ZMod 3) * e a Y) :
    Subsingleton (H1 A) := by
  classical
  letI : Fintype Q := Fintype.ofFinite Q
  by_cases h3 : 3 ∣ Nat.card Q
  swap
  ·
    apply groupCohomology.subsingleton_H1_of_isUnit_card
    rw [← Nat.card_eq_fintype_card]
    exact isUnit_natCast_of_not_dvd h3

  rw [Nat.card_eq_fintype_card] at h3
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 h3
  set P : Subgroup Q := Subgroup.zpowers u with hP
  haveI : P.FiniteIndex := Subgroup.finiteIndex_of_finite
  have hidx : ¬ 3 ∣ P.index := by
    intro hd
    apply h9
    have hc := P.card_mul_index
    rw [hP, Nat.card_zpowers, hu] at hc
    rw [← hc, show (9 : ℕ) = 3 * 3 from rfl]
    exact Nat.mul_dvd_mul_left 3 hd
  have hu3 : u ^ 3 = 1 := hu ▸ pow_orderOf_eq_one u
  have hufin : IsOfFinOrder u := by
    rw [← orderOf_pos_iff, hu]; norm_num

  apply subsingleton_H1_of_forall
  intro x
  suffices hm : ∃ m : A, x u = A.ρ u m - m by
    obtain ⟨m, hm⟩ := hm
    exact exists_of_exists_subgroup A P (isUnit_natCast_of_not_dvd hidx) x m
      (eq_on_zpowers A x u hufin m hm)

  have hv := sq_sub_one_apply_eq_zero A x u hu3
  set w : Module.End k V := σ u⁻¹ with hw
  set w' : Module.End k V := σ u with hw'
  have hww' : w * w' = 1 := by rw [hw, hw', ← map_mul, inv_mul_cancel, map_one]
  have hw'w : w' * w = 1 := by rw [hw, hw', ← map_mul, mul_inv_cancel, map_one]
  have hw3 : w ^ 3 = 1 := by rw [hw, ← map_pow, inv_pow, hu3, inv_one, map_one]
  have hw1 : w ≠ 1 := by
    intro h1
    have : u⁻¹ = 1 := hσ (by rw [← hw, h1, map_one])
    rw [inv_eq_one] at this
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hχu : χ u = 1 := units_eq_one_of_pow_three _ (by rw [← map_pow, hu3, map_one])

  have hmem : ∀ X : Module.End k V, X ∈ LinearMap.ker (LinearMap.trace k V) →
      w * X * w' ∈ LinearMap.ker (LinearMap.trace k V) := by
    intro X hX
    rw [LinearMap.mem_ker] at hX ⊢
    rw [LinearMap.trace_mul_comm k (w * X) w', ← mul_assoc, hw'w, one_mul, hX]
  let cadd : LinearMap.ker (LinearMap.trace k V) →+ LinearMap.ker (LinearMap.trace k V) :=
    { toFun := fun X => ⟨w * X * w', hmem X X.2⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' := fun X Y => by apply Subtype.ext; simp [mul_add, add_mul] }
  let c : LinearMap.ker (LinearMap.trace k V) →ₗ[ZMod 3] LinearMap.ker (LinearMap.trace k V) :=
    cadd.toZModLinearMap 3
  have hc : ∀ X : LinearMap.ker (LinearMap.trace k V), ((c X : LinearMap.ker (LinearMap.trace k V)) :
      Module.End k V) = w * X * w' := fun X => rfl
  set D : LinearMap.ker (LinearMap.trace k V) →ₗ[ZMod 3] LinearMap.ker (LinearMap.trace k V) :=
    c - 1 with hD

  have hT : ∀ a : A, e ((A.ρ u - 1) a) = D.dualMap (e a) := by
    intro a
    ext X
    rw [LinearMap.dualMap_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
      LinearMap.sub_apply, hD, LinearMap.sub_apply, Module.End.one_apply, map_sub,
      he u a X (c X) (by rw [hc]), hχu, Units.val_one, one_mul]

  have hkey : LinearMap.ker D ≤ LinearMap.range (D ∘ₗ D) := by
    intro X hX
    rw [LinearMap.mem_ker, hD, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hX
    have hfix : w * (X : Module.End k V) * w' = X := by rw [← hc, hX]
    obtain ⟨Y, hYtr, hY⟩ := jordan hV w w' hw3 hw1 hww' X X.2 hfix
    refine ⟨⟨Y, hYtr⟩, Subtype.ext ?_⟩
    rw [← hY]
    simp only [hD, LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
      Submodule.coe_sub, hc]
    noncomm_ring
  have hv' : D.dualMap (D.dualMap (e (x u))) = 0 := by
    rw [← hT, ← hT, hv, map_zero]
  obtain ⟨g, hg⟩ := exists_dualMap_eq D hkey (e (x u)) hv'
  refine ⟨e.symm g, e.injective ?_⟩
  rw [← hg, ← e.apply_symm_apply g, ← hT, e.apply_symm_apply]
  rfl

end Main

end P2mSyl3

open P2mSyl3 in
theorem solution
    {k : Type} [Field k] [Finite k] [CharP k 3]
    {V : Type} [AddCommGroup V] [Module k V] (hV : Module.finrank k V = 2)
    {Q : Type} [Group Q] [Finite Q] (h9 : ¬ 9 ∣ Nat.card Q)
    (σ : Q →* Module.End k V) (hσ : Function.Injective σ)
    (χ : Q →* (ZMod 3)ˣ)
    [Module (ZMod 3) (LinearMap.ker (LinearMap.trace k V))]
    (A : Rep (ZMod 3) Q)
    (e : A ≃ₗ[ZMod 3] Module.Dual (ZMod 3) (LinearMap.ker (LinearMap.trace k V)))
    (he : ∀ (q : Q) (a : A) (X Y : LinearMap.ker (LinearMap.trace k V)),
      (Y : Module.End k V) = σ q⁻¹ * X * σ q → e (A.ρ q a) X = (χ q : ZMod 3) * e a Y) :
    Subsingleton (H1 A) :=
  main hV h9 σ hσ χ A e he

end S_groupCohomology_subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card
end P2MW
export P2MW.S_groupCohomology_subsingleton_H1_dual_traceZero_twist_of_injective_of_not_nine_dvd_card (solution)
