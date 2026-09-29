-- Prove2me | solution 1 for groupCohomology.natCard_H2_ofMulDistribMulAction_eq_of_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/7b570723-50b7-5c33-b322-a070226da42a

import Mathlib
import Theorems.Thm_groupCohomology_natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite
import Theorems.Thm_groupCohomology_natCard_H2_eq_natCard_of_shortExact_of_iso_trivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_natCard_H2_ofMulDistribMulAction_eq_of_valuation

set_option autoImplicit false
set_option maxHeartbeats 1600000

p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_natCard_H2_ofMulDistribMulAction_eq_of_valuation.groupCohomology"

namespace groupCohomology
p2m_export "groupCohomology" "isMulCocycle₁_of_mem_cocycles₁ H2 IsMulCoboundary₁ IsMulCocycle₂ mem_cocycles₁_iff H1_induction_on H1π_eq_zero_iff d₁₂_hom_apply mem_cocycles₂_iff d₀₁_hom_apply H2_induction_on H2π_eq_zero_iff H1 IsMulCocycle₁ natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite natCard_H2_eq_natCard_of_shortExact_of_iso_trivial"
namespace Br6
p2m_open "groupCohomology"

variable {G : Type} [Group G]

section Generic
variable {k : Type} [CommRing k]

private theorem shortExact_subtype_mkQ (B : Rep.{0} k G) (W : Submodule k B)
    (hW : ∀ g, W ≤ W.comap (B.ρ g)) :
    (ShortComplex.mk (Rep.subtype B W hW) (Rep.mkQ B W hW) (by
      ext x
      change Submodule.Quotient.mk ((x : W) : B) = (0 : B ⧸ W)
      exact (Submodule.Quotient.mk_eq_zero W).2 x.2)).ShortExact where
  exact := by
    rw [← ShortComplex.exact_map_iff_of_faithful (F := forget₂ (Rep k G) (ModuleCat k)),
      ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range W.subtype = LinearMap.ker W.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  mono_f := (Rep.mono_iff_injective _).2 W.injective_subtype
  epi_g := (Rep.epi_iff_surjective _).2 W.mkQ_surjective

end Generic

section MulDistrib
variable {M : Type} [CommGroup M] [MulDistribMulAction G M]

private abbrev toSubmodule (U : Subgroup M) : Submodule ℤ (Rep.ofMulDistribMulAction G M) :=
  (Subgroup.toAddSubgroup U).toIntSubmodule

private theorem mem_toSubmodule_iff (U : Subgroup M) (x : Rep.ofMulDistribMulAction G M) :
    x ∈ toSubmodule (G := G) U ↔ Additive.toMul x ∈ U := Iff.rfl

private theorem le_comap_of_stable (U : Subgroup M) (hUG : ∀ (g : G), ∀ x ∈ U, g • x ∈ U) (g : G) :
    toSubmodule (G := G) U ≤ (toSubmodule (G := G) U).comap ((Rep.ofMulDistribMulAction G M).ρ g) :=
  fun x hx => hUG g _ hx

end MulDistrib

end groupCohomology.Br6

theorem solution
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {M : Type} [CommGroup M] [MulDistribMulAction G M]
    (v : M →* Multiplicative ℤ) (hv : Function.Surjective v)
    (hvG : ∀ (g : G) (x : M), v (g • x) = v x)
    (U V : Subgroup M) (hU : ∀ x, x ∈ U ↔ v x = 1) (hVU : V ≤ U)
    (hVG : ∀ (g : G), ∀ x ∈ V, g • x ∈ V) [(V.subgroupOf U).FiniteIndex]
    (hV1 : ∀ f : G → M, (∀ g, f g ∈ V) → IsMulCocycle₁ f → ∃ x ∈ V, ∀ g, g • x / x = f g)
    (hV2 : ∀ f : G × G → M, (∀ p, f p ∈ V) → IsMulCocycle₂ f →
      ∃ x : G → M, (∀ g, x g ∈ V) ∧ ∀ g h, g • x h / x (g * h) * x g = f (g, h))
    (h90 : ∀ f : G → M, IsMulCocycle₁ f → IsMulCoboundary₁ f) :
    Nat.card (H2 (Rep.ofMulDistribMulAction G M)) = Nat.card G := by
  classical
  open groupCohomology.Br6 in

  have hUG : ∀ (g : G), ∀ x ∈ U, g • x ∈ U := fun g x hx => by
    rw [hU] at hx ⊢
    rw [hvG, hx]
  let A : Rep ℤ G := Rep.ofMulDistribMulAction G M
  let WU : Submodule ℤ A := groupCohomology.Br6.toSubmodule (G := G) U
  have hWU : ∀ g, WU ≤ WU.comap (A.ρ g) := groupCohomology.Br6.le_comap_of_stable U hUG
  let B : Rep ℤ G := A.subrepresentation WU hWU
  let ι : B → M := fun y => Additive.toMul (Subtype.val (show ↥WU from y))
  let WV : Submodule ℤ B := (groupCohomology.Br6.toSubmodule (G := G) V).comap WU.subtype
  have hmemV : ∀ y : B, y ∈ WV ↔ ι y ∈ V := fun _ => Iff.rfl
  have hBρ : ∀ (g : G) (y : B), ι (B.ρ g y) = g • ι y := fun _ _ => rfl
  have hWV : ∀ g, WV ≤ WV.comap (B.ρ g) := fun g y hy => by
    change ι (B.ρ g y) ∈ V
    rw [hBρ]
    exact hVG g _ ((hmemV y).1 hy)
  let C : Rep ℤ G := B.subrepresentation WV hWV
  let κ : C → M := fun z => ι (Subtype.val (show ↥WV from z))
  have hCρ : ∀ (g : G) (z : C), κ (C.ρ g z) = g • κ z := fun _ _ => rfl
  have hκV : ∀ z : C, κ z ∈ V := fun z => (hmemV _).1 (show ↥WV from z).2

  have hX := groupCohomology.Br6.shortExact_subtype_mkQ B WV hWV

  haveI : Subsingleton (H1 C) := by
    refine ⟨fun a b => ?_⟩
    suffices h : ∀ x : H1 C, x = 0 by rw [h a, h b]
    intro x
    induction x using H1_induction_on with | h c =>
    rw [H1π_eq_zero_iff]
    let f : G → M := fun g => κ (c g)
    have hf : IsMulCocycle₁ f := fun g h => by
      have e := congrArg κ ((mem_cocycles₁_iff (⇑c)).1 c.2 g h)

      exact e
    obtain ⟨x, hxV, hx⟩ := hV1 f (fun g => hκV (c g)) hf
    let x' : C := (show ↥WV from ⟨(show ↥WU from ⟨Additive.ofMul x, hVU hxV⟩), (hmemV _).2 hxV⟩)
    refine ⟨x', funext fun g => ?_⟩
    rw [d₀₁_hom_apply]

    apply Subtype.ext; apply Subtype.ext
    change Additive.ofMul (g • x) - Additive.ofMul x = Additive.ofMul (f g)
    rw [← ofMul_div, hx]
  haveI : Subsingleton (H2 C) := by
    refine ⟨fun a b => ?_⟩
    suffices h : ∀ x : H2 C, x = 0 by rw [h a, h b]
    intro x
    induction x using H2_induction_on with | h c =>
    rw [H2π_eq_zero_iff]
    let f : G × G → M := fun q => κ (c q)
    have hf : IsMulCocycle₂ f := fun g h j => by
      have e := congrArg κ ((mem_cocycles₂_iff (⇑c)).1 c.2 g h j)
      exact e
    obtain ⟨x, hxV, hx⟩ := hV2 f (fun q => hκV (c q)) hf
    let x' : G → C := fun g =>
      (show ↥WV from ⟨(show ↥WU from ⟨Additive.ofMul (x g), hVU (hxV g)⟩), (hmemV _).2 (hxV g)⟩)
    refine ⟨x', funext fun q => ?_⟩
    obtain ⟨g, h⟩ := q
    rw [d₁₂_hom_apply]
    apply Subtype.ext; apply Subtype.ext
    change Additive.ofMul (g • x h) - Additive.ofMul (x (g * h)) + Additive.ofMul (x g) = Additive.ofMul (f (g, h))
    rw [← ofMul_div, ← ofMul_mul, hx]

  haveI : Finite (B.quotient WV hWV) := by
    haveI : Finite (U ⧸ V.subgroupOf U) := Subgroup.finite_quotient_of_finiteIndex
    change Finite (B ⧸ WV)
    let φ : U → B := fun u => (show ↥WU from ⟨Additive.ofMul (u : M), u.2⟩)
    have hφ : Function.Surjective φ := fun y => ⟨⟨ι y, (show ↥WU from y).2⟩, rfl⟩
    refine Finite.of_surjective (Quotient.map' φ (fun u u' huu' => ?_) : U ⧸ V.subgroupOf U → B ⧸ WV) ?_
    · rw [Submodule.quotientRel_def]
      have h := QuotientGroup.leftRel_apply.1 huu'
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h
      have h2 := V.inv_mem h
      rw [mul_inv_rev, inv_inv, mul_comm] at h2
      change (u : M) / (u' : M) ∈ V
      rw [div_eq_mul_inv]
      exact h2
    · intro q
      induction q using Quotient.inductionOn' with | h y =>
      obtain ⟨u, rfl⟩ := hφ y
      exact ⟨Quotient.mk'' u, rfl⟩
  obtain ⟨hF1, hF2, hUeq⟩ :=
    groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite hX

  have hY := groupCohomology.Br6.shortExact_subtype_mkQ A WU hWU
  let vZ : Additive M →+ ℤ :=
    { toFun := fun x => Multiplicative.toAdd (v (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun x y => by simp [toMul_add, map_mul, toAdd_mul] }
  have hvZ : ∀ x, vZ x = Multiplicative.toAdd (v (Additive.toMul x)) := fun _ => rfl
  let vL : A →ₗ[ℤ] ℤ := vZ.toIntLinearMap
  have hvL : ∀ x : A, vL x = Multiplicative.toAdd (v (Additive.toMul (show Additive M from x))) := fun _ => rfl
  have hker : LinearMap.ker vL = WU := by
    ext x
    rw [LinearMap.mem_ker, hvL]
    change _ ↔ Additive.toMul (show Additive M from x) ∈ U
    rw [hU]
    constructor
    · intro h; exact Multiplicative.toAdd.injective (by rw [h]; rfl)
    · intro h; rw [h]; rfl
  have hsurj : Function.Surjective vL := fun n => by
    obtain ⟨m, hm⟩ := hv (Multiplicative.ofAdd n)
    exact ⟨(Additive.ofMul m : Additive M), by rw [hvL]; change Multiplicative.toAdd (v m) = n; rw [hm]; rfl⟩
  let L : (A ⧸ WU) ≃ₗ[ℤ] ℤ :=
    (Submodule.quotEquivOfEq WU (LinearMap.ker vL) hker.symm).trans (vL.quotKerEquivOfSurjective hsurj)
  have hLmk : ∀ y : A, L (Submodule.Quotient.mk y) = vL y := fun y => rfl
  have hL : ∀ (g : G) (q : A ⧸ WU), L ((A.ρ.quotient WU hWU g) q) = L q := by
    intro g q
    induction q using Submodule.Quotient.induction_on with | H x =>
    change L (Submodule.Quotient.mk (A.ρ g x)) = L (Submodule.Quotient.mk x)
    rw [hLmk, hLmk, hvL, hvL]
    change Multiplicative.toAdd (v (g • Additive.toMul (show Additive M from x))) = _
    rw [hvG]
  let E : (A.ρ.quotient WU hWU).Equiv (Representation.trivial ℤ G ℤ) :=
    Representation.Equiv.mk' ⟨L.toLinearMap, fun g => LinearMap.ext fun q => by
      change L (A.ρ.quotient WU hWU g q) = L q
      exact hL g q⟩
      L.symm (fun q => L.symm_apply_apply q) (fun n => L.apply_symm_apply n)
  let e : (A.quotient WU hWU) ≅ Rep.trivial ℤ G ℤ := Rep.mkIso E

  haveI : Subsingleton (H1 A) := by
    refine ⟨fun a b => ?_⟩
    suffices h : ∀ x : H1 A, x = 0 by rw [h a, h b]
    intro x
    induction x using H1_induction_on with | h c =>
    rw [H1π_eq_zero_iff]
    obtain ⟨y, hy⟩ := h90 _ (isMulCocycle₁_of_mem_cocycles₁ (M := M) (⇑c) c.2)
    refine ⟨(Additive.ofMul y : Additive M), funext fun g => ?_⟩
    rw [d₀₁_hom_apply]
    exact hy g
  haveI := hF1
  haveI := hF2
  exact (groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial hY e hUeq).2

end S_groupCohomology_natCard_H2_ofMulDistribMulAction_eq_of_valuation
end P2MW
export P2MW.S_groupCohomology_natCard_H2_ofMulDistribMulAction_eq_of_valuation (solution)
