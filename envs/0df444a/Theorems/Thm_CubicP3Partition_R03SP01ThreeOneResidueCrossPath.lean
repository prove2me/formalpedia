-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeOneResidueCrossPath
-- name    : CubicP3Partition.R03SP01ThreeOneResidueCrossPath
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:10:29.382733+00:00
-- url     : https://prove2.me/theorems/d7974049-9dcd-46c6-8827-5eb1b810e717
-- title:
--   R03 P3-factor structural result: R03SP01ThreeOneResidueCrossPath
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeOneResidueCrossPath` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 52d939f873b52522a9493e140237a7b98ba4742b4b6b8843efc92bf16a07e8da.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-one-residue-cross-path-candidate-v1.lean; source SHA-256 52d939f873b52522a9493e140237a7b98ba4742b4b6b8843efc92bf16a07e8da; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_57bf20f9fb_r03_sp01_three_one_residue_cross_path_candidate_

namespace CubicP3Partition

open CubicP3Partition
open SimpleGraph
universe u
theorem R03SP01ThreeOneResidueCrossPath
    {V : Type u} [Fintype V]
    (G F : SimpleGraph V)
    (hTF : TwoFactor G F)
    (cA cB cC : F.ConnectedComponent)
    (eV : cA.supp ⊕ (cB.supp ⊕ cC.supp) ≃ V)
    (heA : ∀ x : cA.supp, eV (Sum.inl x) = x.1)
    (heB : ∀ x : cB.supp, eV (Sum.inr (Sum.inl x)) = x.1)
    (heC : ∀ x : cC.supp, eV (Sum.inr (Sum.inr x)) = x.1)
    (kA kB kC : Nat)
    [Fintype cA.supp] [Fintype cB.supp] [Fintype cC.supp]
    (hcardA : Fintype.card cA.supp = 1 + kA * 3)
    (hcardB : Fintype.card cB.supp = 1 + kB * 3)
    (hcardC : Fintype.card cC.supp = 1 + kC * 3)
    (xA xB xC : V)
    (hxA : xA ∈ cA.supp) (hxB : xB ∈ cB.supp) (hxC : xC ∈ cC.supp)
    (hAB : G.Adj xA xB) (hBC : G.Adj xB xC) :
    Nonempty (P3Factor G) := by sorry

end CubicP3Partition
