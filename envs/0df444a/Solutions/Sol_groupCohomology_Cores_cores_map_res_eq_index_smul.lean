-- Prove2me | solution 1 for groupCohomology.Cores.cores_map_res_eq_index_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/4314bbf3-e800-5ad8-b5a0-4d0224d8701a

import Mathlib
import Definitions.Def_GroupCohomology_Corestriction2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_Cores_cores_map_res_eq_index_smul

set_option autoImplicit false
p2m_open "CategoryTheory groupCohomology P2MW.S_groupCohomology_Cores_cores_map_res_eq_index_smul.groupCohomology"

attribute [local instance] groupCohomology.Cores.fintypeQuot

namespace groupCohomology
p2m_export "groupCohomology" "d₁₂ H2 H2π H2π_comp_map congr cocycles₂ d₁₂_hom_apply map cocycles mem_cocycles₂_iff H2_induction_on H2π_eq_zero_iff Cores.Transversal Cores.fintypeQuot Cores.cores"
p2m_open "groupCohomology"
namespace Cores
p2m_export "groupCohomology.Cores" "Transversal Transversal.qinv Transversal.qinv_σ_inv_mul fintypeQuot cor₂ cor₂_apply res_mem_cocycles₂ cores cores_H2π"
p2m_open "groupCohomology.Cores"
section Sol
variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G} [H.FiniteIndex] (A : Rep.{0} k G) (τ : Transversal H)

noncomputable def bres (f : G × G → A) : G → A := fun g =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q) (f ((τ.σ q)⁻¹, g) - f ((τ.lam ((τ.σ q)⁻¹ * g) : G), (τ.σ (g⁻¹ • q))⁻¹))

theorem index_smul_sub_cor₂_res {f : G × G → A} (hf : f ∈ cocycles₂ A) :
    (H.index • f - cor₂ A τ (fun hh => f ((hh.1 : G), (hh.2 : G)))) = (d₁₂ A).hom (bres A τ f) := by
  rw [mem_cocycles₂_iff] at hf
  funext gh
  obtain ⟨g₁, g₂⟩ := gh
  simp only [Pi.sub_apply, Pi.smul_apply, cor₂_apply, d₁₂_hom_apply, bres, map_sum]

  rw [show H.index • f (g₁, g₂) = ∑ q : G ⧸ H, f (g₁, g₂) by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]; rfl]

  have hre : ∑ q : G ⧸ H, A.ρ g₁ (A.ρ (τ.σ q) (f ((τ.σ q)⁻¹, g₂) - f ((τ.lam ((τ.σ q)⁻¹ * g₂) : G), (τ.σ (g₂⁻¹ • q))⁻¹))) =
      ∑ q : G ⧸ H, A.ρ g₁ (A.ρ (τ.σ (g₁⁻¹ • q)) (f ((τ.σ (g₁⁻¹ • q))⁻¹, g₂) -
        f ((τ.lam ((τ.σ (g₁⁻¹ • q))⁻¹ * g₂) : G), (τ.σ (g₂⁻¹ • (g₁⁻¹ • q)))⁻¹))) :=
    (Fintype.sum_equiv (MulAction.toPerm g₁⁻¹) _ _ fun q => rfl).symm
  rw [hre, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_

  set x : G := (τ.σ q)⁻¹ with hx
  set x' : G := (τ.σ (g₁⁻¹ • q))⁻¹ with hx'
  set x'' : G := (τ.σ (g₂⁻¹ • (g₁⁻¹ • q)))⁻¹ with hx''
  have hσ : (τ.σ (Transversal.qinv (H := H) (x * g₁)))⁻¹ = x' := by rw [hx, Transversal.qinv_σ_inv_mul, ← hx']
  have hσ' : (τ.σ (Transversal.qinv (H := H) (x' * g₂)))⁻¹ = x'' := by rw [hx', Transversal.qinv_σ_inv_mul, ← hx'']
  have hq'' : (g₁ * g₂)⁻¹ • q = g₂⁻¹ • (g₁⁻¹ • q) := by rw [mul_inv_rev, mul_smul]
  have hab : τ.lam (x * g₁ * g₂) = τ.lam (x * g₁) * τ.lam (x' * g₂) := by rw [τ.lam_mul (x * g₁) g₂, hσ]

  set A₁ : G := (τ.lam (x * g₁) : G) with hA₁
  set B₂ : G := (τ.lam (x' * g₂) : G) with hB₂
  have rel1 : x * g₁ = A₁ * x' := by have := τ.lam_mul_σ_inv (x * g₁); rw [hσ] at this; exact this.symm
  have rel2 : x' * g₂ = B₂ * x'' := by have := τ.lam_mul_σ_inv (x' * g₂); rw [hσ'] at this; exact this.symm
  have hgσ : A.ρ g₁ * A.ρ (τ.σ (g₁⁻¹ • q)) = A.ρ (τ.σ q) * A.ρ A₁ := by
    rw [← map_mul, ← map_mul]; exact congrArg _ (τ.mul_σ q g₁)
  have hxσ : A.ρ (τ.σ q) (A.ρ x (f (g₁, g₂))) = f (g₁, g₂) := by
    rw [← Module.End.mul_apply, ← map_mul, hx, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [show x * (g₁ * g₂) = x * g₁ * g₂ from (mul_assoc _ _ _).symm, hab, inv_mul_cancel_left, hq'', ← Module.End.mul_apply, hgσ,
    Module.End.mul_apply, ← hxσ]
  simp only [Subgroup.coe_mul, ← hA₁, ← hB₂, ← map_add, ← map_sub]
  congr 1

  have C1 := hf x g₁ g₂
  have C2 := hf A₁ x' g₂
  have C3 := hf A₁ B₂ x''
  rw [rel1] at C1
  rw [rel2] at C2

  rw [map_sub]
  have e1 : A.ρ x (f (g₁, g₂)) = f (A₁ * x', g₂) + f (x, g₁) - f (x, g₁ * g₂) := eq_sub_of_add_eq C1.symm
  have e2 : A.ρ A₁ (f (x', g₂)) = f (A₁ * x', g₂) + f (A₁, x') - f (A₁, B₂ * x'') := eq_sub_of_add_eq C2.symm
  have e3 : A.ρ A₁ (f (B₂, x'')) = f (A₁ * B₂, x'') + f (A₁, B₂) - f (A₁, B₂ * x'') := eq_sub_of_add_eq C3.symm
  rw [e1, e2, e3]
  abel

theorem cores_res (f : cocycles₂ A) :
    cores A τ (H2π _ ⟨_, res_mem_cocycles₂ A f.2⟩) = H.index • H2π A f := by
  rw [cores_H2π, ← map_nsmul, eq_comm, ← sub_eq_zero, ← map_sub, H2π_eq_zero_iff]
  exact ⟨bres A τ f, (index_smul_sub_cor₂_res A τ f.2).symm⟩

theorem map_res_H2π (f : cocycles₂ A) :
    (map H.subtype (𝟙 (Rep.res H.subtype A)) 2).hom (H2π A f) = H2π (Rep.res H.subtype A) ⟨_, res_mem_cocycles₂ A f.2⟩ := by
  have h1 := congrArg (fun φ => ModuleCat.Hom.hom φ f) (H2π_comp_map (A := A) (B := Rep.res H.subtype A) H.subtype (𝟙 _))
  dsimp only at h1
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h1
  rw [h1]
  rfl

end Sol
end Cores
end groupCohomology

open CategoryTheory _root_.groupCohomology _root_.P2MW.S_groupCohomology_Cores_cores_map_res_eq_index_smul.groupCohomology in
theorem solution
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (H : Subgroup G) [H.FiniteIndex] (τ : Cores.Transversal H) (x : H2 A) :
    Cores.cores A τ ((map H.subtype (𝟙 (Rep.res H.subtype A)) 2).hom x) = H.index • x := by
  induction x using H2_induction_on with
  | h f => rw [Cores.map_res_H2π]; exact Cores.cores_res A τ f

end S_groupCohomology_Cores_cores_map_res_eq_index_smul
end P2MW
export P2MW.S_groupCohomology_Cores_cores_map_res_eq_index_smul (solution)
