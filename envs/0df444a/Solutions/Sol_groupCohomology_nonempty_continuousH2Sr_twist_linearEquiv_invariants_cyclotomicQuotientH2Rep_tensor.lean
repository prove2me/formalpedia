-- Prove2me | solution 1 for groupCohomology.nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/328180b3-e254-5acf-9569-46affd5b7c28

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_Rep_QuotientRightTranslation
import Definitions.Def_GroupCohomology_CyclotomicQuotientH2Rep
import Theorems.Thm_groupCohomology_exists_continuousH2Sr_trivial_tensor_linearEquiv
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField.LevelArith TensorProduct

namespace P2mS25PCollapse

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory"

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {k : Type} [Field k] {G : Type} [Group G] (Λ : Subgroup G) [Λ.Normal] [Λ.FiniteIndex]
variable (χ : G →* kˣ) (N : Rep.{0} k G) (hN : ∀ g : G, g ∈ Λ → N.ρ g = 1)

noncomputable scoped instance : Fintype (G ⧸ Λ) := Fintype.ofFinite _

noncomputable def ρbar : G ⧸ Λ →* (N →ₗ[k] N) :=
  QuotientGroup.lift Λ N.ρ (fun g hg => by rw [MonoidHom.mem_ker]; exact hN g hg)

@[scoped simp] lemma ρbar_mk (g : G) : ρbar Λ N hN (g : G ⧸ Λ) = N.ρ g := rfl

noncomputable abbrev P : Rep.{0} k G := Rep.ofMulActionFinsupp k G (G ⧸ Λ)
noncomputable abbrev P1 : Rep.{0} k G := (P (k := k) Λ).twist χ
noncomputable abbrev N0 : Rep.{0} k G := Rep.trivial k G N
noncomputable abbrev X : Rep.{0} k G := N0 (k := k) N ⊗ P1 Λ χ

noncomputable def endTriv (φ : N →ₗ[k] N) : N0 (k := k) (G := G) N ⟶ N0 N :=
  Rep.ofHom ⟨φ, fun g => rfl⟩

@[scoped simp] lemma endTriv_hom_apply (φ : N →ₗ[k] N) (n : N) : (endTriv N φ : N0 (k := k) (G := G) N ⟶ N0 N).hom n = φ n := rfl

noncomputable def T (d : G ⧸ Λ) : X Λ χ N ⟶ X Λ χ N :=
  endTriv N (ρbar Λ N hN d) ⊗ₘ Rep.quotientRightTranslationTwist Λ χ d

lemma T_hom_tmul (d : G ⧸ Λ) (n : N) (x : G ⧸ Λ →₀ k) :
    (T Λ χ N hN d).hom (n ⊗ₜ[k] x) = (ρbar Λ N hN d n) ⊗ₜ[k] (Finsupp.mapDomain (· * d⁻¹) x) := rfl

lemma X_ρ_tmul (g : G) (n : N) (x : G ⧸ Λ →₀ k) :
    (X Λ χ N).ρ g (n ⊗ₜ[k] x) = n ⊗ₜ[k] ((χ g : k) • Finsupp.lmapDomain k k (fun q : G ⧸ Λ => (g : G ⧸ Λ) * q) x) := by
  rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul]
  congr 1

noncomputable def ιLin : N →ₗ[k] N ⊗[k] (G ⧸ Λ →₀ k) :=
  ∑ c : G ⧸ Λ, ((TensorProduct.mk k N (G ⧸ Λ →₀ k)).flip (Finsupp.single c 1)) ∘ₗ ρbar Λ N hN c⁻¹

lemma ιLin_apply (n : N) : ιLin Λ N hN n = ∑ c : G ⧸ Λ, ρbar Λ N hN c⁻¹ n ⊗ₜ[k] Finsupp.single c (1 : k) := by
  simp [ιLin, LinearMap.sum_apply]

noncomputable def ι : N.twist χ ⟶ X Λ χ N :=
  Rep.ofHom ⟨ιLin Λ N hN, fun g => by
    apply LinearMap.ext; intro n
    change ιLin Λ N hN ((N.ρ.twist χ) g n) = (X Λ χ N).ρ g (ιLin Λ N hN n)
    rw [Representation.twist_apply_apply, map_smul, ιLin_apply, ιLin_apply, map_sum, Finset.smul_sum]
    have hc : ∀ c : G ⧸ Λ, (X Λ χ N).ρ g (ρbar Λ N hN c⁻¹ n ⊗ₜ[k] Finsupp.single c (1 : k)) =
        (χ g : k) • (ρbar Λ N hN c⁻¹ n ⊗ₜ[k] Finsupp.single ((g : G ⧸ Λ) * c) (1 : k)) := fun c => by
      rw [X_ρ_tmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, TensorProduct.tmul_smul]
    rw [Finset.sum_congr rfl fun c _ => hc c]
    refine Fintype.sum_equiv (Equiv.mulLeft (g : G ⧸ Λ)⁻¹) _ _ fun c => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_cancel_left]
    congr 2
    rw [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply, ρbar_mk]⟩

lemma ι_hom_apply (n : N) : (ι Λ χ N hN).hom n = ∑ c : G ⧸ Λ, ρbar Λ N hN c⁻¹ n ⊗ₜ[k] Finsupp.single c (1 : k) :=
  ιLin_apply Λ N hN n

noncomputable def πBil : N →ₗ[k] (G ⧸ Λ →₀ k) →ₗ[k] N :=
  (Finsupp.lift (N →ₗ[k] N) k (G ⧸ Λ) fun c => ρbar Λ N hN c).flip

lemma πBil_apply_single (m : N) (c : G ⧸ Λ) (a : k) : πBil Λ N hN m (Finsupp.single c a) = a • ρbar Λ N hN c m := by
  simp [πBil, Finsupp.lift_apply]

noncomputable def πLin : N ⊗[k] (G ⧸ Λ →₀ k) →ₗ[k] N :=
  (Fintype.card (G ⧸ Λ) : k)⁻¹ • TensorProduct.lift (πBil Λ N hN)

lemma πLin_tmul_single (m : N) (c : G ⧸ Λ) (a : k) :
    πLin Λ N hN (m ⊗ₜ[k] Finsupp.single c a) = (Fintype.card (G ⧸ Λ) : k)⁻¹ • (a • ρbar Λ N hN c m) := by
  simp only [πLin, LinearMap.smul_apply, TensorProduct.lift.tmul, πBil_apply_single]

noncomputable def π : X Λ χ N ⟶ N.twist χ :=
  Rep.ofHom ⟨πLin Λ N hN, fun g => by
    apply TensorProduct.ext'
    intro m x
    change πLin Λ N hN ((X Λ χ N).ρ g (m ⊗ₜ[k] x)) = (N.ρ.twist χ) g (πLin Λ N hN (m ⊗ₜ[k] x))
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, hx, hy]
    | single c a =>
      rw [X_ρ_tmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, TensorProduct.tmul_smul, map_smul,
        πLin_tmul_single, πLin_tmul_single, Representation.twist_apply_apply, map_smul, map_smul,
        ← ρbar_mk Λ N hN g, ← Module.End.mul_apply, ← map_mul]⟩

lemma π_hom_tmul_single (m : N) (c : G ⧸ Λ) (a : k) :
    (π Λ χ N hN).hom (m ⊗ₜ[k] Finsupp.single c a) = (Fintype.card (G ⧸ Λ) : k)⁻¹ • (a • ρbar Λ N hN c m) :=
  πLin_tmul_single Λ N hN m c a

lemma ι_T (d : G ⧸ Λ) : ι Λ χ N hN ≫ T Λ χ N hN d = ι Λ χ N hN := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun n => ?_
  change (T Λ χ N hN d).hom ((ι Λ χ N hN).hom n) = (ι Λ χ N hN).hom n
  rw [ι_hom_apply, map_sum]
  have h1 : ∀ c : G ⧸ Λ, (T Λ χ N hN d).hom (ρbar Λ N hN c⁻¹ n ⊗ₜ[k] Finsupp.single c (1 : k)) =
      ρbar Λ N hN (d * c⁻¹) n ⊗ₜ[k] Finsupp.single (c * d⁻¹) (1 : k) := fun c => by
    rw [T_hom_tmul, Finsupp.mapDomain_single, ← Module.End.mul_apply, ← map_mul]
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  refine Fintype.sum_equiv (Equiv.mulRight d⁻¹) _ _ fun c => ?_
  simp only [Equiv.coe_mulRight, mul_inv_rev, inv_inv]

variable (hinv : (Fintype.card (G ⧸ Λ) : k) ≠ 0)
include hinv

lemma ι_π : ι Λ χ N hN ≫ π Λ χ N hN = 𝟙 _ := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun n => ?_
  change (π Λ χ N hN).hom ((ι Λ χ N hN).hom n) = n
  rw [ι_hom_apply, map_sum]
  have h1 : ∀ c : G ⧸ Λ, (π Λ χ N hN).hom (ρbar Λ N hN c⁻¹ n ⊗ₜ[k] Finsupp.single c (1 : k)) =
      (Fintype.card (G ⧸ Λ) : k)⁻¹ • n := fun c => by
    rw [π_hom_tmul_single, one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [Finset.sum_congr rfl fun c _ => h1 c]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k, smul_smul, mul_inv_cancel₀ hinv, one_smul]

omit hinv in

lemma ι_π_hom : (ι Λ χ N hN).hom.toLinearMap ∘ₗ (π Λ χ N hN).hom.toLinearMap =
    (Fintype.card (G ⧸ Λ) : k)⁻¹ • ∑ d : G ⧸ Λ, (T Λ χ N hN d).hom.toLinearMap := by
  apply TensorProduct.ext'
  intro m x
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | single c a =>
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply]
    change (ι Λ χ N hN).hom ((π Λ χ N hN).hom (m ⊗ₜ[k] Finsupp.single c a)) =
      (Fintype.card (G ⧸ Λ) : k)⁻¹ • ∑ d : G ⧸ Λ, (T Λ χ N hN d).hom (m ⊗ₜ[k] Finsupp.single c a)
    rw [π_hom_tmul_single, map_smul, map_smul, ι_hom_apply]
    congr 1
    have h1 : ∀ c' : G ⧸ Λ, ρbar Λ N hN c'⁻¹ (ρbar Λ N hN c m) ⊗ₜ[k] Finsupp.single c' (1 : k) =
        ρbar Λ N hN (c'⁻¹ * c) m ⊗ₜ[k] Finsupp.single c' (1 : k) := fun c' => by
      rw [← Module.End.mul_apply, ← map_mul]
    have h2 : ∀ d : G ⧸ Λ, (T Λ χ N hN d).hom (m ⊗ₜ[k] Finsupp.single c a) =
        a • (ρbar Λ N hN d m ⊗ₜ[k] Finsupp.single (c * d⁻¹) (1 : k)) := fun d => by
      rw [T_hom_tmul, Finsupp.mapDomain_single, ← TensorProduct.tmul_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [Finset.sum_congr rfl fun c' _ => h1 c', Finset.sum_congr rfl fun d _ => h2 d, ← Finset.smul_sum]
    congr 1

    refine (Fintype.sum_equiv ((Equiv.inv (G ⧸ Λ)).trans (Equiv.mulLeft c)) _ _ fun d => ?_).symm
    simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulLeft, mul_inv_rev, inv_inv, inv_mul_cancel_right]

end P2mS25PCollapse
p2m_reactivate "P2MW.S_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor.P2mS25PCollapse"

namespace P2mS25PCollapse

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory groupCohomology"

variable {k : Type} [Field k] {G : Type} [Group G]
variable (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)

lemma H2map_eq_smul_sum {A B : Rep.{0} k G} {ιx : Type} [Fintype ιx] (f : A ⟶ B) (g : ιx → (A ⟶ B)) (a : k)
    (h : f.hom.toLinearMap = a • ∑ d, (g d).hom.toLinearMap) :
    continuousH2SrMapHom S r f = a • ∑ d, continuousH2SrMapHom S r (g d) := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.sum_apply]
  change continuousH2SrMapHom S r f (continuousH2Srπ r S A x) =
    a • ∑ d, continuousH2SrMapHom S r (g d) (continuousH2Srπ r S A x)
  simp only [continuousH2SrMapHom_continuousH2Srπ]
  rw [← map_sum, ← map_smul]
  congr 1
  apply Subtype.ext
  funext st
  have := LinearMap.congr_fun h ((x : G × G → A) st)
  simp only [LinearMap.smul_apply, LinearMap.sum_apply] at this
  rw [Submodule.coe_smul, Submodule.coe_sum, Pi.smul_apply, Finset.sum_apply]
  exact this

variable (Λ : Subgroup G) [Λ.Normal] [Λ.FiniteIndex]
variable (χ : G →* kˣ) (N : Rep.{0} k G) [FiniteDimensional k N] (hN : ∀ g : G, g ∈ Λ → N.ρ g = 1)
variable (hinv : (Fintype.card (G ⧸ Λ) : k) ≠ 0)

def Wfix : Submodule k (N ⊗[k] continuousH2Sr r S (P1 Λ χ)) where
  carrier := {w | ∀ c : G, TensorProduct.map (N.ρ c)
    (continuousH2SrMapHom S r (Rep.quotientRightTranslationTwist Λ χ (c : G ⧸ Λ))) w = w}
  zero_mem' := fun c => map_zero _
  add_mem' := fun {v w} hv hw c => by rw [map_add, hv c, hw c]
  smul_mem' := fun a w hw c => by rw [map_smul, hw c]

lemma mem_Wfix_iff (w : N ⊗[k] continuousH2Sr r S (P1 Λ χ)) :
    w ∈ Wfix r S Λ χ N ↔ ∀ c : G, TensorProduct.map (N.ρ c)
      (continuousH2SrMapHom S r (Rep.quotientRightTranslationTwist Λ χ (c : G ⧸ Λ))) w = w := Iff.rfl

include hN hinv in

theorem nonempty_linearEquiv_Wfix :
    Nonempty (continuousH2Sr r S (N.twist χ) ≃ₗ[k] ↥(Wfix r S Λ χ N)) := by
  obtain ⟨Θ, -, hΘ⟩ := groupCohomology.exists_continuousH2Sr_trivial_tensor_linearEquiv r S N (P1 Λ χ)

  let f := continuousH2SrMapHom S r (ι Λ χ N hN)
  let g := continuousH2SrMapHom S r (π Λ χ N hN)
  have hgf : g ∘ₗ f = LinearMap.id := by
    rw [← continuousH2SrMapHom_comp, ι_π Λ χ N hN hinv, continuousH2SrMapHom_id]
  have hf : Function.Injective f := Function.LeftInverse.injective (g := g) fun x => LinearMap.congr_fun hgf x

  have hnat : ∀ (c : G) (y : continuousH2Sr r S (X Λ χ N)),
      Θ (continuousH2SrMapHom S r (T Λ χ N hN (c : G ⧸ Λ)) y) =
        TensorProduct.map (N.ρ c) (continuousH2SrMapHom S r (Rep.quotientRightTranslationTwist Λ χ (c : G ⧸ Λ))) (Θ y) :=
    fun c y => LinearMap.congr_fun (hΘ (N.ρ c) (Rep.quotientRightTranslationTwist Λ χ (c : G ⧸ Λ)) (T Λ χ N hN (c : G ⧸ Λ))
      (fun v x => rfl)) y

  have hrange : (LinearMap.range f).map Θ.toLinearMap = Wfix r S Λ χ N := by
    ext w
    constructor
    · rintro ⟨y, ⟨x, rfl⟩, rfl⟩ c
      rw [LinearEquiv.coe_coe, ← hnat]
      congr 1
      change (continuousH2SrMapHom S r (T Λ χ N hN (c : G ⧸ Λ)) ∘ₗ continuousH2SrMapHom S r (ι Λ χ N hN)) x = _
      rw [← continuousH2SrMapHom_comp, ι_T]
    · intro hw
      refine ⟨Θ.symm w, ⟨g (Θ.symm w), ?_⟩, Θ.apply_symm_apply w⟩

      change (f ∘ₗ g) (Θ.symm w) = Θ.symm w
      have hfg : f ∘ₗ g = (Fintype.card (G ⧸ Λ) : k)⁻¹ • ∑ d : G ⧸ Λ, continuousH2SrMapHom S r (T Λ χ N hN d) := by
        rw [← continuousH2SrMapHom_comp]
        exact H2map_eq_smul_sum r S _ _ _ (ι_π_hom Λ χ N hN)
      rw [hfg, LinearMap.smul_apply, LinearMap.sum_apply]
      apply Θ.injective
      rw [map_smul, map_sum]
      have hd : ∀ d : G ⧸ Λ, Θ (continuousH2SrMapHom S r (T Λ χ N hN d) (Θ.symm w)) = w := fun d => by
        induction d using QuotientGroup.induction_on with
        | H c => rw [hnat, Θ.apply_symm_apply]; exact hw c
      rw [Finset.sum_congr rfl fun d _ => hd d, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul k,
        smul_smul, inv_mul_cancel₀ hinv, one_smul, Θ.apply_symm_apply]
  exact ⟨(LinearEquiv.ofInjective f hf).trans ((Θ.submoduleMap (LinearMap.range f)).trans (LinearEquiv.ofEq _ _ hrange))⟩

end P2mS25PCollapse
p2m_reactivate "P2MW.S_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor.P2mS25PCollapse"

namespace P2mS25PCollapse

open scoped TensorProduct
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory groupCohomology"

variable {k : Type} [Field k] {G : Type} [Group G]
variable (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
variable (Λ : Subgroup G) [Λ.Normal] [Λ.FiniteIndex]
variable (χ : G →* kˣ) (N : Rep.{0} k G) [FiniteDimensional k N] (hN : ∀ g : G, g ∈ Λ → N.ρ g = 1)
variable (hinv : (Fintype.card (G ⧸ Λ) : k) ≠ 0)

include hN hinv in
theorem nonempty_linearEquiv_invariants (σ : Representation k G (continuousH2Sr r S (P1 Λ χ)))
    (hσ : ∀ (c : G) (x : continuousH2Sr r S (P1 Λ χ)),
      σ c x = continuousH2SrMapHom S r (Rep.quotientRightTranslationTwist Λ χ (c : G ⧸ Λ)) x) :
    Nonempty (continuousH2Sr r S (N.twist χ) ≃ₗ[k] (Rep.of σ ⊗ N : Rep.{0} k G).ρ.invariants) := by
  obtain ⟨E⟩ := nonempty_linearEquiv_Wfix r S Λ χ N hN hinv
  let β := TensorProduct.comm k N (continuousH2Sr r S (P1 Λ χ))
  have hσ' : ∀ c : G, σ c = continuousH2SrMapHom S r (Rep.quotientRightTranslationTwist Λ χ (c : G ⧸ Λ)) :=
    fun c => LinearMap.ext (hσ c)
  have hβ : (Wfix r S Λ χ N).map β.toLinearMap = (Rep.of σ ⊗ N : Rep.{0} k G).ρ.invariants := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩ c
      rw [Rep.tensor_ρ, Representation.tprod_apply]
      change TensorProduct.map (σ c) (N.ρ c) (β w) = β w
      rw [hσ', ← LinearEquiv.coe_toLinearMap β, ← LinearMap.comp_apply, TensorProduct.map_comp_comm_eq, LinearMap.comp_apply,
        (mem_Wfix_iff r S Λ χ N w).1 hw c]
    · intro z hz
      refine ⟨β.symm z, fun c => ?_, β.apply_symm_apply z⟩
      have hzc := hz c
      rw [Rep.tensor_ρ, Representation.tprod_apply] at hzc
      change TensorProduct.map (σ c) (N.ρ c) z = z at hzc
      apply β.injective
      rw [β.apply_symm_apply, ← LinearEquiv.coe_toLinearMap β, ← LinearMap.comp_apply, ← TensorProduct.map_comp_comm_eq,
        LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, β.apply_symm_apply, ← hσ', hzc]
  exact ⟨E.trans ((β.submoduleMap _).trans (LinearEquiv.ofEq _ _ hβ))⟩

end P2mS25PCollapse
p2m_reactivate "P2MW.S_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor.P2mS25PCollapse"

open P2mS25PCollapse in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal] [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).FiniteIndex]
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup → N.ρ s = 1) :
    Nonempty (continuousH2Sr K.fixingSubgroup.subtype S (N.twist ((cycloChar p).comp K.fixingSubgroup.subtype)) ≃ₗ[ZMod p]
      (cyclotomicQuotientH2Rep S K L p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants) := by

  have hinv : (Fintype.card (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) : ZMod p) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card]
    change ((L.fixingSubgroup.relIndex K.fixingSubgroup : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hcop.symm
  have hN : ∀ g : ↥K.fixingSubgroup, g ∈ L.fixingSubgroup.subgroupOf K.fixingSubgroup → N.ρ g = 1 :=
    fun g hg => htriv g (Subgroup.mem_subgroupOf.1 hg)
  exact nonempty_linearEquiv_invariants K.fixingSubgroup.subtype S (L.fixingSubgroup.subgroupOf K.fixingSubgroup)
    ((cycloChar p).comp K.fixingSubgroup.subtype) N hN hinv (cyclotomicQuotientH2ρ S K L p) (fun c x => rfl)

end S_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor
end P2MW
export P2MW.S_groupCohomology_nonempty_continuousH2Sr_twist_linearEquiv_invariants_cyclotomicQuotientH2Rep_tensor (solution)
