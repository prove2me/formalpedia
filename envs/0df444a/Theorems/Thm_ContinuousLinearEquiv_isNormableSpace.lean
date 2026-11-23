-- Prove2me | Theorems.Thm_ContinuousLinearEquiv_isNormableSpace
-- name    : ContinuousLinearEquiv.isNormableSpace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:16.186706+00:00
-- url     : https://prove2.me/theorems/db889073-a44c-4ac5-b9ec-9cfd41aea706
-- title:
--   Continuous Linear Equiv: is Normable Space
-- statement:
--   The Continuous Linear Equiv construction uses the is Normable Space property established by this source lemma. The formal statement records the complete hypotheses and conclusion. Separately attributed Apache-2.0 Mathlib compatibility backport at commit 9d581dfff2e41de989072ea63abf3daf69311520; target API and same-field transport specializations are explicit in the checked statement.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/LocallyConvex/WithSeminorms.lean

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_ImportCompatibility_Normability
set_option autoImplicit true
open Topology
variable {𝕜 E F : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]

theorem ContinuousLinearEquiv.isNormableSpace [IsNormableSpace 𝕜 F]
    [TopologicalSpace E] (f : E ≃L[𝕜] F) : IsNormableSpace 𝕜 E := by sorry
