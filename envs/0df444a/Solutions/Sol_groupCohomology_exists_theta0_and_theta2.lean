-- Prove2me | solution 1 for groupCohomology.exists_theta0_and_theta2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/051b0fc6-c97f-5ae0-a294-ceba160d73d9

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_exists_theta0_and_theta2

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

open CategoryTheory groupCohomology

theorem solution
    {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {M D N : Rep.{u} k G} (φ : M →ₗ[k] D →ₗ[k] N) (hφ : Rep.IsEquivariantBilinear M D N φ)
    (inv : continuousH2 r N →ₗ[k] k) :
    (∃ θ₀ : M.ρ.invariants →ₗ[k] Module.Dual k (continuousH2 r D), IsTheta0 r φ inv θ₀) ∧
    (∃ θ₂ : continuousH2 r M →ₗ[k] Module.Dual k D.ρ.invariants, IsTheta2 r φ inv θ₂) := by
  classical

  let PR : D.ρ.invariants → (continuousH2 r M →ₗ[k] continuousH2 r N) := fun d =>
    continuousH2Map (MonoidHom.id G) (fun _ => rfl) (φ.flip (d : D)) (fun g m => by
      show φ (M.ρ g m) (d : D) = N.ρ g (φ m (d : D))
      conv_lhs => rw [← d.2 g]
      exact hφ g m d)
  have PR_π : ∀ (d : D.ρ.invariants) (z : levelCocycles₂ r M),
      PR d (continuousH2π r M z) = continuousH2π r N (levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) (φ.flip (d : D))
        (fun g m => by
          show φ (M.ρ g m) (d : D) = N.ρ g (φ m (d : D))
          conv_lhs => rw [← d.2 g]
          exact hφ g m d) z) := fun _ _ => rfl

  let PL : M.ρ.invariants → (continuousH2 r D →ₗ[k] continuousH2 r N) := fun m =>
    continuousH2Map (MonoidHom.id G) (fun _ => rfl) (φ (m : M)) (fun g x => by
      show φ (m : M) (D.ρ g x) = N.ρ g (φ (m : M) x)
      conv_lhs => rw [← m.2 g]
      exact hφ g m x)
  have PL_π : ∀ (m : M.ρ.invariants) (z : levelCocycles₂ r D),
      PL m (continuousH2π r D z) = continuousH2π r N (levelCocycles₂Map (MonoidHom.id G) (fun _ => rfl) (φ (m : M))
        (fun g x => by
          show φ (m : M) (D.ρ g x) = N.ρ g (φ (m : M) x)
          conv_lhs => rw [← m.2 g]
          exact hφ g m x) z) := fun _ _ => rfl
  refine ⟨⟨{ toFun := fun m => inv ∘ₗ PL m
             map_add' := fun m m' => by
               apply LinearMap.ext; intro w
               induction w using Submodule.Quotient.induction_on with | _ z =>
               show inv (PL (m + m') (continuousH2π r D z)) = inv (PL m (continuousH2π r D z)) + inv (PL m' (continuousH2π r D z))
               rw [PL_π, PL_π, PL_π, ← map_add, ← map_add]
               congr 2
               apply Subtype.ext; funext st
               show φ ((m : M) + m') ((z : G × G → D) st) = φ (m : M) ((z : G × G → D) st) + φ (m' : M) ((z : G × G → D) st)
               rw [map_add, LinearMap.add_apply]
             map_smul' := fun c m => by
               apply LinearMap.ext; intro w
               induction w using Submodule.Quotient.induction_on with | _ z =>
               show inv (PL (c • m) (continuousH2π r D z)) = c • inv (PL m (continuousH2π r D z))
               rw [PL_π, PL_π, ← map_smul, ← map_smul]
               congr 2
               apply Subtype.ext; funext st
               show φ (c • (m : M)) ((z : G × G → D) st) = c • φ (m : M) ((z : G × G → D) st)
               rw [map_smul, LinearMap.smul_apply] }, ?_⟩, ⟨LinearMap.mk₂ k (fun x d => inv (PR d x))
      (fun x x' d => by simp only [map_add])
      (fun c x d => by simp only [map_smul, smul_eq_mul])
      (fun x d d' => by
        induction x using Submodule.Quotient.induction_on with | _ z =>
        show inv (PR (d + d') (continuousH2π r M z)) = inv (PR d (continuousH2π r M z)) + inv (PR d' (continuousH2π r M z))
        rw [PR_π, PR_π, PR_π, ← map_add, ← map_add]
        congr 2
        apply Subtype.ext; funext st
        show φ ((z : G × G → M) st) ((d : D) + d') = φ ((z : G × G → M) st) (d : D) + φ ((z : G × G → M) st) (d' : D)
        rw [map_add])
      (fun c x d => by
        induction x using Submodule.Quotient.induction_on with | _ z =>
        show inv (PR (c • d) (continuousH2π r M z)) = c • inv (PR d (continuousH2π r M z))
        rw [PR_π, PR_π, ← map_smul, ← map_smul]
        congr 2
        apply Subtype.ext; funext st
        show φ ((z : G × G → M) st) (c • (d : D)) = c • φ ((z : G × G → M) st) (d : D)
        rw [map_smul]), ?_⟩⟩
  ·
    intro m z e he
    show inv (PL m (continuousH2π r D z)) = inv (continuousH2π r N e)
    rw [PL_π]
    congr 2
    apply Subtype.ext; funext st
    exact (he st).symm
  ·
    intro z d e he
    show inv (PR d (continuousH2π r M z)) = inv (continuousH2π r N e)
    rw [PR_π]
    congr 2
    apply Subtype.ext; funext st
    exact (he st).symm

end S_groupCohomology_exists_theta0_and_theta2
end P2MW
export P2MW.S_groupCohomology_exists_theta0_and_theta2 (solution)
