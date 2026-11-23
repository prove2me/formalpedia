-- Prove2me | Theorems.Thm_Formalism_L2_SG_PoincareSeriesSquareIntegrable_mem_stab
-- name    : Formalism.L2.SG.PoincareSeriesSquareIntegrable.mem_stab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:29.686961+00:00
-- url     : https://prove2.me/theorems/afe49686-7f2e-4f18-9ce6-ba6a8ab54e85
-- title:
--   Poincare Series Square Integrable: mem stab
-- statement:
--   The Poincare Series Square Integrable construction uses the mem stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/PoincareSeriesSquareIntegrable.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/PoincareSeriesSquareIntegrable.lean#L30-L34

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_FoldBound
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_PoincareSeriesSquareIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.dupNamespace false
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.PoincareSeriesSquareIntegrable
open Formalism.L2.SG.FoldBound

theorem Formalism.L2.SG.PoincareSeriesSquareIntegrable.mem_stab {G : Type*} [Group G] (S S' : Subgroup G) (γ g : G) :
    g ∈ stab S S' γ ↔ g ∈ S ∧ γ⁻¹ * g * γ ∈ S' := by sorry
