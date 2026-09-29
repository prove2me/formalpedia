-- Prove2me | Theorems.Thm_CubicP3Partition_R03SP01ThreeComponentSupportEquiv
-- name    : CubicP3Partition.R03SP01ThreeComponentSupportEquiv
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:08:57.52743+00:00
-- url     : https://prove2.me/theorems/9f9657c5-8c9b-4121-bba8-71943715cf95
-- title:
--   R03 P3-factor structural result: R03SP01ThreeComponentSupportEquiv
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `CubicP3Partition.R03SP01ThreeComponentSupportEquiv` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 7382c05fae98800d33bedbfc059dd4180a7817293408180b4a0afb6196465b5c.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp01/r03-sp01-three-component-support-equiv-candidate-v1.lean; source SHA-256 7382c05fae98800d33bedbfc059dd4180a7817293408180b4a0afb6196465b5c; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Definitions.Def_cubic_p3_partition_models
import Definitions.Def_r03_defs_999a973085_r03_sp01_three_component_support_equiv_candidate

namespace CubicP3Partition

open CubicP3Partition
open SimpleGraph
universe u
theorem R03SP01ThreeComponentSupportEquiv
    {V : Type u} [Fintype V]
    (F : SimpleGraph V)
    (cA cB cC : F.ConnectedComponent)
    (hAB : cA ≠ cB) (hAC : cA ≠ cC) (hBC : cB ≠ cC)
    (hcover : ∀ v : V,
      v ∈ cA.supp ∨ v ∈ cB.supp ∨ v ∈ cC.supp) :
    ∃ (eV : cA.supp ⊕ (cB.supp ⊕ cC.supp) ≃ V),
      (∀ x : cA.supp, eV (Sum.inl x) = x.1) ∧
      (∀ x : cB.supp, eV (Sum.inr (Sum.inl x)) = x.1) ∧
      (∀ x : cC.supp, eV (Sum.inr (Sum.inr x)) = x.1) := by sorry

end CubicP3Partition
