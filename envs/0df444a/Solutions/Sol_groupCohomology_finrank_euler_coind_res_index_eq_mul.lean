-- Prove2me | solution 1 for groupCohomology.finrank_euler_coind_res_index_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/e31c003d-53f2-5e79-918f-a8d49997e536

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Theorems.Thm_groupCohomology_finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective
import Theorems.Thm_Rep_exists_coind_res_linearEquiv_quotient_fun
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_finrank_euler_coind_res_index_eq_mul

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory

namespace P2mS26HIND
open groupCohomology Polynomial

variable {k S : Type u} [Field k] [Group S] (S'' : Subgroup S) [S''.Normal] (N : Rep.{u} k S)

noncomputable def ρW : Representation k S (S ⧸ S'' → N) where
  toFun s :=
    { toFun := fun F q => N.ρ s (F (q * (s : S ⧸ S'')))
      map_add' := fun F F' => by funext q; exact map_add _ _ _
      map_smul' := fun c F => by funext q; exact map_smul _ _ _ }
  map_one' := by
    apply LinearMap.ext; intro F; funext q
    show N.ρ 1 (F (q * ((1 : S) : S ⧸ S''))) = F q
    rw [map_one, QuotientGroup.mk_one, mul_one]; rfl
  map_mul' s s' := by
    apply LinearMap.ext; intro F; funext q
    show N.ρ (s * s') (F (q * ((s * s' : S) : S ⧸ S''))) = N.ρ s (N.ρ s' (F (q * (s : S ⧸ S'') * (s' : S ⧸ S''))))
    rw [map_mul, Module.End.mul_apply, QuotientGroup.mk_mul, mul_assoc]

lemma ρW_apply (s : S) (F : S ⧸ S'' → N) (q : S ⧸ S'') : ρW S'' N s F q = N.ρ s (F (q * (s : S ⧸ S''))) := rfl

noncomputable abbrev W : Rep.{u} k S := Rep.of (ρW S'' N)

end P2mS26HIND

namespace P2mS26HIND
open groupCohomology Polynomial

variable {k S : Type u} [Field k] [Group S] (S'' : Subgroup S) [S''.Normal] (N : Rep.{u} k S)

noncomputable def τL (t : S ⧸ S'') : Module.End k (S ⧸ S'' → N) :=
  { toFun := fun F q => F (q * t), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

lemma τL_apply (t : S ⧸ S'') (F : S ⧸ S'' → N) (q : S ⧸ S'') : τL S'' N t F q = F (q * t) := rfl

lemma τL_pow_apply (t : S ⧸ S'') (n : ℕ) (F : S ⧸ S'' → N) (q : S ⧸ S'') :
    (τL S'' N t ^ n) F q = F (q * t ^ n) := by
  induction n generalizing q with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, τL_apply, ih, mul_assoc, ← pow_succ']

noncomputable def DL (t : S ⧸ S'') : Module.End k (S ⧸ S'' → N) := τL S'' N t - 1

lemma DL_apply (t : S ⧸ S'') (F : S ⧸ S'' → N) (q : S ⧸ S'') : DL S'' N t F q = F (q * t) - F q := rfl

lemma DL_ρW (t : S ⧸ S'') (ht : ∀ q : S ⧸ S'', q * t = t * q) (s : S) (F : S ⧸ S'' → N) :
    DL S'' N t (ρW S'' N s F) = ρW S'' N s (DL S'' N t F) := by
  funext q
  rw [DL_apply, ρW_apply, ρW_apply, ρW_apply, DL_apply, map_sub, mul_assoc, ← ht, ← mul_assoc]

lemma DL_pow_ρW (t : S ⧸ S'') (ht : ∀ q : S ⧸ S'', q * t = t * q) (n : ℕ) (s : S) (F : S ⧸ S'' → N) :
    (DL S'' N t ^ n) (ρW S'' N s F) = ρW S'' N s ((DL S'' N t ^ n) F) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, DL_ρW S'' N t ht]

lemma DL_pow_eq_zero (p : ℕ) [Fact p.Prime] [CharP k p] (t : S ⧸ S'') (htp : t ^ p = 1) :
    DL S'' N t ^ p = 0 := by
  have hpoly : ((X : k[X]) - 1) ^ p = X ^ p - 1 := by
    rw [sub_pow_char, one_pow]
  have h1 : Polynomial.aeval (τL S'' N t) (((X : k[X]) - 1) ^ p) = DL S'' N t ^ p := by
    rw [map_pow, map_sub, aeval_X, map_one]; rfl
  have h2 : Polynomial.aeval (τL S'' N t) ((X : k[X]) ^ p - 1) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero]
    apply LinearMap.ext; intro F; funext q
    rw [τL_pow_apply, htp, mul_one, Module.End.one_apply]
  rw [← h1, hpoly, h2]

lemma DL_eq_zero_iff (t : S ⧸ S'') (hgen : ∀ q : S ⧸ S'', ∃ n : ℕ, q = t ^ n) (F : S ⧸ S'' → N) :
    DL S'' N t F = 0 ↔ ∀ q, F q = F 1 := by
  constructor
  · intro h q
    have hstep : ∀ q, F (q * t) = F q := fun q => by
      have := congrFun h q; rw [DL_apply, Pi.zero_apply, sub_eq_zero] at this; exact this
    obtain ⟨n, rfl⟩ := hgen q
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← one_mul (t ^ n * t), ← mul_assoc, hstep, one_mul, ih]
  · intro h
    funext q
    rw [DL_apply, h (q * t), h q, sub_self, Pi.zero_apply]

end P2mS26HIND

namespace P2mS26HIND
open groupCohomology

variable {k S : Type u} [Field k] [Group S] (S'' : Subgroup S) [S''.Normal] (N : Rep.{u} k S)
  (t : S ⧸ S'') (ht : ∀ q : S ⧸ S'', q * t = t * q)

noncomputable def Wsub (j : ℕ) : Submodule k (S ⧸ S'' → N) := LinearMap.ker (DL S'' N t ^ j)

lemma mem_Wsub (j : ℕ) (F : S ⧸ S'' → N) : F ∈ Wsub S'' N t j ↔ (DL S'' N t ^ j) F = 0 := LinearMap.mem_ker

include ht in
lemma Wsub_le_comap (j : ℕ) (s : S) : Wsub S'' N t j ≤ (Wsub S'' N t j).comap (ρW S'' N s) := by
  intro F hF
  rw [Submodule.mem_comap, mem_Wsub, DL_pow_ρW S'' N t ht, (mem_Wsub _ _ _ _ _).1 hF, map_zero]

noncomputable abbrev Wrep (j : ℕ) : Rep.{u} k S :=
  Rep.of ((ρW S'' N).subrepresentation (Wsub S'' N t j) (Wsub_le_comap S'' N t ht j))

lemma DL_mem_Wsub (j : ℕ) (F : S ⧸ S'' → N) (hF : F ∈ Wsub S'' N t (j + 1)) : DL S'' N t F ∈ Wsub S'' N t j := by
  rw [mem_Wsub] at hF ⊢
  rwa [pow_succ, Module.End.mul_apply] at hF

lemma const_mem_Wsub (j : ℕ) (n : N) : (fun _ : S ⧸ S'' => n) ∈ Wsub S'' N t (j + 1) := by
  rw [mem_Wsub, pow_succ, Module.End.mul_apply]
  have : DL S'' N t (fun _ : S ⧸ S'' => n) = 0 := by funext q; rw [DL_apply, sub_self]; rfl
  rw [this, map_zero]

noncomputable def ψL (j : ℕ) : Wsub S'' N t (j + 1) →ₗ[k] Wsub S'' N t j :=
  (DL S'' N t).restrict (p := Wsub S'' N t (j + 1)) (q := Wsub S'' N t j) (fun F hF => DL_mem_Wsub S'' N t j F hF)

include ht in
lemma ψL_comm (j : ℕ) (s : S) (F : Wsub S'' N t (j + 1)) :
    ψL S'' N t j ((Wrep S'' N t ht (j + 1)).ρ s F) = (Wrep S'' N t ht j).ρ s (ψL S'' N t j F) := by
  apply Subtype.ext
  exact DL_ρW S'' N t ht s F

noncomputable def ψ (j : ℕ) : Wrep S'' N t ht (j + 1) ⟶ Wrep S'' N t ht j :=
  Rep.ofHom ((ψL S'' N t j).intertwiningMap_of_isIntertwiningMap
    (Wrep S'' N t ht (j + 1)).ρ (Wrep S'' N t ht j).ρ (ψL_comm S'' N t ht j))

lemma ψ_apply (j : ℕ) (F : Wrep S'' N t ht (j + 1)) :
    ((ψ S'' N t ht j).hom F : S ⧸ S'' → N) = DL S'' N t (F : S ⧸ S'' → N) := rfl

noncomputable def φL (j : ℕ) : N →ₗ[k] Wsub S'' N t (j + 1) :=
  { toFun := fun n => ⟨fun _ => n, const_mem_Wsub S'' N t j n⟩
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

include ht in
lemma φL_comm (j : ℕ) (s : S) (n : N) :
    φL S'' N t j (N.ρ s n) = (Wrep S'' N t ht (j + 1)).ρ s (φL S'' N t j n) := by
  apply Subtype.ext
  funext q
  rfl

noncomputable def φ (j : ℕ) : N ⟶ Wrep S'' N t ht (j + 1) :=
  Rep.ofHom ((φL S'' N t j).intertwiningMap_of_isIntertwiningMap N.ρ (Wrep S'' N t ht (j + 1)).ρ (φL_comm S'' N t ht j))

lemma φ_apply (j : ℕ) (n : N) (q : S ⧸ S'') : ((φ S'' N t ht j).hom n : S ⧸ S'' → N) q = n := rfl

lemma φ_injective (j : ℕ) : Function.Injective (φ S'' N t ht j).hom := fun n n' h => by
  have := congrArg (fun F : Wrep S'' N t ht (j + 1) => (F : S ⧸ S'' → N) 1) h
  exact this

lemma exact_φ_ψ (hgen : ∀ q : S ⧸ S'', ∃ n : ℕ, q = t ^ n) (j : ℕ) (F : Wrep S'' N t ht (j + 1)) :
    (ψ S'' N t ht j).hom F = 0 ↔ ∃ n : N, (φ S'' N t ht j).hom n = F := by
  constructor
  · intro h
    have h' : DL S'' N t (F : S ⧸ S'' → N) = 0 := by
      have := congrArg Subtype.val h; rwa [ψ_apply] at this
    rw [DL_eq_zero_iff S'' N t hgen] at h'
    refine ⟨(F : S ⧸ S'' → N) 1, Subtype.ext (funext fun q => ?_)⟩
    rw [φ_apply]; exact (h' q).symm
  · rintro ⟨n, rfl⟩
    apply Subtype.ext
    rw [ψ_apply]
    funext q
    show ((φ S'' N t ht j).hom n : S ⧸ S'' → N) (q * t) - ((φ S'' N t ht j).hom n : S ⧸ S'' → N) q = 0
    rw [φ_apply, φ_apply, sub_self]

variable [FiniteDimensional k N] [Finite (S ⧸ S'')]

lemma finrank_Wsub_succ_eq (hgen : ∀ q : S ⧸ S'', ∃ n : ℕ, q = t ^ n) (j : ℕ) :
    Module.finrank k (Wsub S'' N t (j + 1))
      = Module.finrank k N + Module.finrank k (LinearMap.range (ψ S'' N t ht j).hom.toLinearMap) := by
  classical
  have rn := LinearMap.finrank_range_add_finrank_ker (ψ S'' N t ht j).hom.toLinearMap

  have e : N ≃ₗ[k] LinearMap.ker (ψ S'' N t ht j).hom.toLinearMap :=
    { toFun := fun n => ⟨(φ S'' N t ht j).hom n, by
        rw [LinearMap.mem_ker]; exact (exact_φ_ψ S'' N t ht hgen j _).2 ⟨n, rfl⟩⟩
      map_add' := fun _ _ => by apply Subtype.ext; exact map_add _ _ _
      map_smul' := fun _ _ => by apply Subtype.ext; exact map_smul _ _ _
      invFun := fun F => ((F : Wrep S'' N t ht (j + 1)) : S ⧸ S'' → N) 1
      left_inv := fun n => rfl
      right_inv := fun F => by
        obtain ⟨n, hn⟩ := (exact_φ_ψ S'' N t ht hgen j _).1 (LinearMap.mem_ker.1 F.2)
        apply Subtype.ext
        show (φ S'' N t ht j).hom (((F : Wrep S'' N t ht (j + 1)) : S ⧸ S'' → N) 1) = (F : Wrep S'' N t ht (j + 1))
        rw [← hn]
        rfl }
  rw [← e.finrank_eq] at rn
  have : Module.finrank k (Wrep S'' N t ht (j + 1)) = Module.finrank k (Wsub S'' N t (j + 1)) := rfl
  omega

include ht in
lemma finrank_Wsub_succ_le (hgen : ∀ q : S ⧸ S'', ∃ n : ℕ, q = t ^ n) (j : ℕ) :
    Module.finrank k (Wsub S'' N t (j + 1)) ≤ Module.finrank k N + Module.finrank k (Wsub S'' N t j) := by
  rw [finrank_Wsub_succ_eq S'' N t ht hgen j]
  exact Nat.add_le_add_left (Submodule.finrank_le _) _

include ht in
lemma finrank_Wsub_add_le (hgen : ∀ q : S ⧸ S'', ∃ n : ℕ, q = t ^ n) (j i : ℕ) :
    Module.finrank k (Wsub S'' N t (j + i)) ≤ Module.finrank k (Wsub S'' N t j) + i * Module.finrank k N := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := finrank_Wsub_succ_le S'' N t ht hgen (j + i)
    rw [← add_assoc]
    rw [Nat.succ_mul]
    omega

lemma finrank_Wsub_top (p : ℕ) [Fact p.Prime] [CharP k p] (htp : t ^ p = 1) (hcard : Nat.card (S ⧸ S'') = p) :
    Module.finrank k (Wsub S'' N t p) = p * Module.finrank k N := by
  classical
  letI : Fintype (S ⧸ S'') := Fintype.ofFinite _
  have htop : Wsub S'' N t p = ⊤ := by
    rw [Wsub, DL_pow_eq_zero S'' N p t htp, LinearMap.ker_zero]
  rw [htop, finrank_top, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card, hcard]

include ht in

lemma finrank_Wsub_eq (p : ℕ) [Fact p.Prime] [CharP k p] (htp : t ^ p = 1) (hcard : Nat.card (S ⧸ S'') = p)
    (hgen : ∀ q : S ⧸ S'', ∃ n : ℕ, q = t ^ n) (j : ℕ) (hj : j ≤ p) :
    Module.finrank k (Wsub S'' N t j) = j * Module.finrank k N := by
  have h0 : Module.finrank k (Wsub S'' N t 0) = 0 := by
    have : Wsub S'' N t 0 = ⊥ := by
      ext F; rw [mem_Wsub, pow_zero, Module.End.one_apply, Submodule.mem_bot]
    rw [this, finrank_bot]
  have up : Module.finrank k (Wsub S'' N t j) ≤ j * Module.finrank k N := by
    have := finrank_Wsub_add_le S'' N t ht hgen 0 j
    rw [zero_add, h0, zero_add] at this
    exact this
  have down : Module.finrank k (Wsub S'' N t p)
      ≤ Module.finrank k (Wsub S'' N t j) + (p - j) * Module.finrank k N := by
    have := finrank_Wsub_add_le S'' N t ht hgen j (p - j)
    rwa [Nat.add_sub_cancel' hj] at this
  rw [finrank_Wsub_top S'' N t p htp hcard] at down

  have hsplit : p * Module.finrank k N = j * Module.finrank k N + (p - j) * Module.finrank k N := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' hj]
  omega

end P2mS26HIND

namespace P2mS26HIND
open groupCohomology

variable {k S : Type u} [Field k] [Group S] (S'' : Subgroup S) [S''.Normal] (N : Rep.{u} k S)
  (t : S ⧸ S'') (ht : ∀ q : S ⧸ S'', q * t = t * q) [FiniteDimensional k N] [Finite (S ⧸ S'')]

lemma ψ_surjective (p : ℕ) [Fact p.Prime] [CharP k p] (htp : t ^ p = 1) (hcard : Nat.card (S ⧸ S'') = p)
    (hgen : ∀ q : S ⧸ S'', ∃ n : ℕ, q = t ^ n) (j : ℕ) (hj : j + 1 ≤ p) :
    Function.Surjective (ψ S'' N t ht j).hom := by
  have h1 := finrank_Wsub_succ_eq S'' N t ht hgen j
  rw [finrank_Wsub_eq S'' N t ht p htp hcard hgen (j + 1) hj] at h1
  have h2 := finrank_Wsub_eq S'' N t ht p htp hcard hgen j (Nat.le_of_succ_le hj)
  have hr : Module.finrank k (LinearMap.range (ψ S'' N t ht j).hom.toLinearMap)
      = Module.finrank k (Wsub S'' N t j) := by
    rw [h2]; rw [Nat.succ_mul] at h1; omega
  have htop : LinearMap.range (ψ S'' N t ht j).hom.toLinearMap = ⊤ := Submodule.eq_top_of_finrank_eq hr
  exact LinearMap.range_eq_top.1 htop

end P2mS26HIND

namespace P2mS26HIND
open groupCohomology

variable {k S : Type u} [Field k] [Group S]
  (rS : S →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))

lemma finrank_eq_of_inverse {A B : Rep.{u} k S} (α : A ⟶ B) (β : B ⟶ A)
    (hβα : ∀ a, β.hom (α.hom a) = a) (hαβ : ∀ b, α.hom (β.hom b) = b) :
    Module.finrank k A.ρ.invariants = Module.finrank k B.ρ.invariants ∧
    Module.finrank k (continuousH1 rS A) = Module.finrank k (continuousH1 rS B) ∧
    Module.finrank k (continuousH2 rS A) = Module.finrank k (continuousH2 rS B) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  ·
    let f : A.ρ.invariants →ₗ[k] B.ρ.invariants :=
      (α.hom.toLinearMap ∘ₗ A.ρ.invariants.subtype).codRestrict _ fun a g => by
        show B.ρ g (α.hom (a : A)) = α.hom (a : A); rw [← Rep.hom_comm_apply, a.2 g]
    let g : B.ρ.invariants →ₗ[k] A.ρ.invariants :=
      (β.hom.toLinearMap ∘ₗ B.ρ.invariants.subtype).codRestrict _ fun b g => by
        show A.ρ g (β.hom (b : B)) = β.hom (b : B); rw [← Rep.hom_comm_apply, b.2 g]
    exact (LinearEquiv.ofLinear f g (LinearMap.ext fun b => Subtype.ext (hαβ b))
      (LinearMap.ext fun a => Subtype.ext (hβα a))).finrank_eq
  ·
    have cα : ∀ c : cocycles₁ A, (mapCocycles₁ (MonoidHom.id S) α c : S → B) = fun s => α.hom (c s) := fun _ => rfl
    have cβ : ∀ c : cocycles₁ B, (mapCocycles₁ (MonoidHom.id S) β c : S → A) = fun s => β.hom (c s) := fun _ => rfl
    have Hα : ∀ c : cocycles₁ A, (map (MonoidHom.id S) α 1).hom ((H1π A).hom c)
        = (H1π B).hom (mapCocycles₁ (MonoidHom.id S) α c) := fun c => H1π_comp_map_apply _ _ c
    have Hβ : ∀ c : cocycles₁ B, (map (MonoidHom.id S) β 1).hom ((H1π B).hom c)
        = (H1π A).hom (mapCocycles₁ (MonoidHom.id S) β c) := fun c => H1π_comp_map_apply _ _ c
    have mα : ∀ x : continuousH1 rS A, (map (MonoidHom.id S) α 1).hom (x : H1 A) ∈ continuousH1 rS B := by
      intro x
      obtain ⟨c, hc, hx⟩ := (mem_continuousH1_iff rS A _).1 x.2
      rw [← hx, Hα]; exact H1π_mem_continuousH1 rS B (by rw [cα]; exact hc.comp _)
    have mβ : ∀ x : continuousH1 rS B, (map (MonoidHom.id S) β 1).hom (x : H1 B) ∈ continuousH1 rS A := by
      intro x
      obtain ⟨c, hc, hx⟩ := (mem_continuousH1_iff rS B _).1 x.2
      rw [← hx, Hβ]; exact H1π_mem_continuousH1 rS A (by rw [cβ]; exact hc.comp _)
    let f : continuousH1 rS A →ₗ[k] continuousH1 rS B :=
      ((map (MonoidHom.id S) α 1).hom ∘ₗ (continuousH1 rS A).subtype).codRestrict _ mα
    let g : continuousH1 rS B →ₗ[k] continuousH1 rS A :=
      ((map (MonoidHom.id S) β 1).hom ∘ₗ (continuousH1 rS B).subtype).codRestrict _ mβ
    have h1 : ∀ x, f (g x) = x := by
      intro x
      obtain ⟨c, -, hx⟩ := (mem_continuousH1_iff rS B _).1 x.2
      apply Subtype.ext
      show (map (MonoidHom.id S) α 1).hom ((map (MonoidHom.id S) β 1).hom (x : H1 B)) = x
      rw [← hx, Hβ, Hα]
      congr 1
      all_goals
        apply cocycles₁_ext
        intro s
        exact ((congrFun (cα _) s).trans (congrArg α.hom (congrFun (cβ c) s))).trans (hαβ (c s))
    have h2 : ∀ x, g (f x) = x := by
      intro x
      obtain ⟨c, -, hx⟩ := (mem_continuousH1_iff rS A _).1 x.2
      apply Subtype.ext
      show (map (MonoidHom.id S) β 1).hom ((map (MonoidHom.id S) α 1).hom (x : H1 A)) = x
      rw [← hx, Hα, Hβ]
      congr 1
      all_goals
        apply cocycles₁_ext
        intro s
        exact ((congrFun (cβ _) s).trans (congrArg β.hom (congrFun (cα c) s))).trans (hβα (c s))
    exact (LinearEquiv.ofLinear f g (LinearMap.ext h1) (LinearMap.ext h2)).finrank_eq
  ·
    let f := continuousH2MapHom rS α
    let g := continuousH2MapHom rS β
    have h1 : ∀ z, f (g z) = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with | _ x =>
      change continuousH2π rS B _ = continuousH2π rS B x
      congr 1
      all_goals
        apply Subtype.ext
        funext q
        exact hαβ _
    have h2 : ∀ z, g (f z) = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with | _ x =>
      change continuousH2π rS A _ = continuousH2π rS A x
      congr 1
      all_goals
        apply Subtype.ext
        funext q
        exact hβα _
    exact (LinearEquiv.ofLinear f g (LinearMap.ext h1) (LinearMap.ext h2)).finrank_eq

lemma smooth_fun (S'' : Subgroup S) [S''.Normal] [Finite (S ⧸ S'')] (N : Rep.{u} k S)
    (hS'' : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap rS ≤ S'')
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, rS s ∈ F.fixingSubgroup → N.ρ s n = n)
    (F : S ⧸ S'' → N) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ u : S, rS u ∈ E.fixingSubgroup → ρW S'' N u F = F := by
  classical
  obtain ⟨F₀, hF₀, hle₀⟩ := hS''
  choose Fq hFq hfix using fun q => hsm (F q)
  haveI := hF₀; haveI := hFq
  haveI : FiniteDimensional ℚ (⨆ q, Fq q : IntermediateField ℚ (AlgebraicClosure ℚ)) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  refine ⟨F₀ ⊔ ⨆ q, Fq q, inferInstance, fun u hu => ?_⟩
  have huS : u ∈ S'' := hle₀ (IntermediateField.fixingSubgroup_antitone le_sup_left hu)
  funext q
  rw [ρW_apply, (QuotientGroup.eq_one_iff u).2 huS, mul_one]
  exact hfix q u (IntermediateField.fixingSubgroup_antitone ((le_iSup Fq q).trans le_sup_right) hu)

end P2mS26HIND

namespace P2mS26HIND
open groupCohomology

variable {k S : Type u} [Field k] [Group S]
  (rS : S →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (S'' : Subgroup S) [S''.Normal] (N : Rep.{u} k S)
  (t : S ⧸ S'') (ht : ∀ q : S ⧸ S'', q * t = t * q) [FiniteDimensional k N] [Finite (S ⧸ S'')]

lemma count (p : ℕ) [Fact p.Prime] [CharP k p] (htp : t ^ p = 1) (hcard : Nat.card (S ⧸ S'') = p)
    (hgen : ∀ q : S ⧸ S'', ∃ n : ℕ, q = t ^ n)
    (hS'' : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap rS ≤ S'')
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, rS s ∈ F.fixingSubgroup → N.ρ s n = n)
    (HFIN : ∀ M : Rep.{u} k S, (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ s : S, rS s ∈ F.fixingSubgroup → M.ρ s m = m) → FiniteDimensional k M →
        FiniteDimensional k (continuousH1 rS M) ∧ FiniteDimensional k (continuousH2 rS M))
    (HD2 : ∀ (B C : Rep.{u} k S) (ψ : B ⟶ C), (∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
        FiniteDimensional ℚ F ∧ ∀ s : S, rS s ∈ F.fixingSubgroup → B.ρ s m = m) → FiniteDimensional k B →
        Function.Surjective ψ.hom → Function.Surjective (continuousH2MapHom rS ψ))
    (j : ℕ) (hj : j ≤ p) :
    Module.finrank k (Wrep S'' N t ht j).ρ.invariants + Module.finrank k (continuousH2 rS (Wrep S'' N t ht j))
        + j * Module.finrank k (continuousH1 rS N)
      = Module.finrank k (continuousH1 rS (Wrep S'' N t ht j)) + j * Module.finrank k N.ρ.invariants
        + j * Module.finrank k (continuousH2 rS N) := by
  classical

  have hsmW : ∀ i, ∀ F : Wrep S'' N t ht i, ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ s : S, rS s ∈ E.fixingSubgroup → (Wrep S'' N t ht i).ρ s F = F := by
    intro i F
    obtain ⟨E, hE, h⟩ := smooth_fun rS S'' N hS'' hsm (F : S ⧸ S'' → N)
    exact ⟨E, hE, fun s hs => Subtype.ext (h s hs)⟩
  obtain ⟨hN1, hN2⟩ := HFIN N hsm inferInstance
  haveI := hN1; haveI := hN2
  induction j with
  | zero =>
    haveI : Subsingleton (Wrep S'' N t ht 0) := ⟨fun a b => by
      apply Subtype.ext
      have ha := a.2; have hb := b.2
      rw [mem_Wsub, pow_zero, Module.End.one_apply] at ha hb
      rw [ha, hb]⟩
    have e0 : Module.finrank k (Wrep S'' N t ht 0).ρ.invariants = 0 := Module.finrank_zero_of_subsingleton
    have e1 : Module.finrank k (continuousH1 rS (Wrep S'' N t ht 0)) = 0 := by
      haveI : Subsingleton (continuousH1 rS (Wrep S'' N t ht 0)) := ⟨fun x y => by
        obtain ⟨c, -, hc⟩ := (mem_continuousH1_iff _ _ _).1 x.2
        obtain ⟨c', -, hc'⟩ := (mem_continuousH1_iff _ _ _).1 y.2
        apply Subtype.ext
        rw [← hc, ← hc', Subsingleton.elim c c']⟩
      exact Module.finrank_zero_of_subsingleton
    have e2 : Module.finrank k (continuousH2 rS (Wrep S'' N t ht 0)) = 0 := by
      haveI : Subsingleton (continuousH2 rS (Wrep S'' N t ht 0)) := ⟨fun a b => by
        induction a using Submodule.Quotient.induction_on with | _ x =>
        induction b using Submodule.Quotient.induction_on with | _ y =>
        rw [Subsingleton.elim x y]⟩
      exact Module.finrank_zero_of_subsingleton
    rw [e0, e1, e2]; simp
  | succ j ih =>
    have ih' := ih (Nat.le_of_succ_le hj)
    obtain ⟨hW1, hW2⟩ := HFIN (Wrep S'' N t ht j) (hsmW j) inferInstance
    obtain ⟨hW1', hW2'⟩ := HFIN (Wrep S'' N t ht (j + 1)) (hsmW (j + 1)) inferInstance
    haveI := hW1; haveI := hW2; haveI := hW1'; haveI := hW2'
    have hsurj := ψ_surjective S'' N t ht p htp hcard hgen j hj
    have add := groupCohomology.finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective rS
      (φ S'' N t ht j) (ψ S'' N t ht j) (φ_injective S'' N t ht j) hsurj (exact_φ_ψ S'' N t ht hgen j)
      (hsmW (j + 1)) (HD2 _ _ (ψ S'' N t ht j) (hsmW (j + 1)) inferInstance hsurj)
    rw [Nat.succ_mul, Nat.succ_mul, Nat.succ_mul]
    omega

end P2mS26HIND

open groupCohomology in
theorem solution {k G : Type u} [Field k] [Group G] (p : ℕ) [Fact p.Prime] [CharP k p]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G)
    (HFIN : ∀ (M : Rep.{u} k S), (∀ m : M, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
          ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → M.ρ s m = m) → FiniteDimensional k M →
        FiniteDimensional k (groupCohomology.continuousH1 (r.comp S.subtype) M) ∧
          FiniteDimensional k (groupCohomology.continuousH2 (r.comp S.subtype) M))
    (HD2 : ∀ (B C : Rep.{u} k S) (ψ : B ⟶ C), (∀ m : B, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
          FiniteDimensional ℚ F ∧ ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → B.ρ s m = m) → FiniteDimensional k B →
        Function.Surjective ψ.hom → Function.Surjective (groupCohomology.continuousH2MapHom (r.comp S.subtype) ψ))
    (S'' : Subgroup S) [S''.Normal]
    (hS'' : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧
      F₀.fixingSubgroup.comap (r.comp S.subtype) ≤ S'')
    (hidx : S''.index = p) (N : Rep.{u} k S)
    (hsm : ∀ n : N, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : S, (r.comp S.subtype) s ∈ F.fixingSubgroup → N.ρ s n = n) [FiniteDimensional k N] :
    Module.finrank k (Rep.coind S''.subtype (Rep.res S''.subtype N)).ρ.invariants
      + Module.finrank k (groupCohomology.continuousH2 (r.comp S.subtype) (Rep.coind S''.subtype (Rep.res S''.subtype N)))
      + p * Module.finrank k (groupCohomology.continuousH1 (r.comp S.subtype) N)
    = Module.finrank k (groupCohomology.continuousH1 (r.comp S.subtype) (Rep.coind S''.subtype (Rep.res S''.subtype N)))
      + p * Module.finrank k N.ρ.invariants
      + p * Module.finrank k (groupCohomology.continuousH2 (r.comp S.subtype) N) := by
  classical
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : S''.FiniteIndex := ⟨by rw [hidx]; exact hp⟩
  haveI : Finite (S ⧸ S'') := Subgroup.finite_quotient_of_finiteIndex
  have hcard : Nat.card (S ⧸ S'') = p := hidx

  haveI : IsCyclic (S ⧸ S'') := isCyclic_of_prime_card hcard
  obtain ⟨t, htgen⟩ := IsCyclic.exists_generator (α := S ⧸ S'')
  have hgen : ∀ q : S ⧸ S'', ∃ n : ℕ, q = t ^ n := by
    intro q
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (htgen q)
    refine ⟨(m % (orderOf t : ℤ)).toNat, ?_⟩
    have h0 : 0 ≤ m % (orderOf t : ℤ) := Int.emod_nonneg _ (by
      have := (IsOfFinOrder.orderOf_pos (isOfFinOrder_of_finite t)).ne'; exact_mod_cast this)
    rw [← hm, ← zpow_natCast, Int.toNat_of_nonneg h0, zpow_mod_orderOf]
  have ht : ∀ q : S ⧸ S'', q * t = t * q := by
    intro q; obtain ⟨n, rfl⟩ := hgen q; exact (Commute.pow_self t n).eq
  have htp : t ^ p = 1 := by rw [← hcard]; exact pow_card_eq_one'

  obtain ⟨e, he⟩ := Rep.exists_coind_res_linearEquiv_quotient_fun S'' N
  have hαcomm : ∀ (s : S) (f : (Rep.coind S''.subtype (Rep.res S''.subtype N))), e ((Rep.coind S''.subtype (Rep.res S''.subtype N)).ρ s f) = P2mS26HIND.ρW S'' N s (e f) := fun s f => funext fun q => he s f q
  have hβcomm : ∀ (s : S) (F : S ⧸ S'' → N), e.symm (P2mS26HIND.ρW S'' N s F) = (Rep.coind S''.subtype (Rep.res S''.subtype N)).ρ s (e.symm F) := by
    intro s F
    apply e.injective
    rw [e.apply_symm_apply, hαcomm, e.apply_symm_apply]
  let α : (Rep.coind S''.subtype (Rep.res S''.subtype N)) ⟶ P2mS26HIND.W S'' N :=
    Rep.ofHom (e.toLinearMap.intertwiningMap_of_isIntertwiningMap (Rep.coind S''.subtype (Rep.res S''.subtype N)).ρ (P2mS26HIND.ρW S'' N) hαcomm)
  let β : P2mS26HIND.W S'' N ⟶ (Rep.coind S''.subtype (Rep.res S''.subtype N)) :=
    Rep.ofHom (e.symm.toLinearMap.intertwiningMap_of_isIntertwiningMap (P2mS26HIND.ρW S'' N) (Rep.coind S''.subtype (Rep.res S''.subtype N)).ρ hβcomm)
  obtain ⟨i0, i1, i2⟩ := P2mS26HIND.finrank_eq_of_inverse (r.comp S.subtype) α β
    (fun a => e.symm_apply_apply a) (fun b => e.apply_symm_apply b)

  have htop : P2mS26HIND.Wsub S'' N t p = ⊤ := by
    rw [P2mS26HIND.Wsub, P2mS26HIND.DL_pow_eq_zero S'' N p t htp, LinearMap.ker_zero]
  let α' : P2mS26HIND.Wrep S'' N t ht p ⟶ P2mS26HIND.W S'' N :=
    Rep.ofHom ((P2mS26HIND.Wsub S'' N t p).subtype.intertwiningMap_of_isIntertwiningMap
      (P2mS26HIND.Wrep S'' N t ht p).ρ (P2mS26HIND.ρW S'' N) (fun _ _ => rfl))
  let β' : P2mS26HIND.W S'' N ⟶ P2mS26HIND.Wrep S'' N t ht p :=
    Rep.ofHom ((LinearMap.id.codRestrict (P2mS26HIND.Wsub S'' N t p) (fun F => htop ▸ Submodule.mem_top) :
        (S ⧸ S'' → N) →ₗ[k] P2mS26HIND.Wsub S'' N t p).intertwiningMap_of_isIntertwiningMap
      (P2mS26HIND.ρW S'' N) (P2mS26HIND.Wrep S'' N t ht p).ρ (fun _ _ => rfl))
  obtain ⟨j0, j1, j2⟩ := P2mS26HIND.finrank_eq_of_inverse (r.comp S.subtype) α' β'
    (fun a => Subtype.ext rfl) (fun b => rfl)

  have cnt := P2mS26HIND.count (r.comp S.subtype) S'' N t ht p htp hcard hgen hS'' hsm HFIN HD2 p le_rfl
  omega

end S_groupCohomology_finrank_euler_coind_res_index_eq_mul
end P2MW
export P2MW.S_groupCohomology_finrank_euler_coind_res_index_eq_mul (solution)
