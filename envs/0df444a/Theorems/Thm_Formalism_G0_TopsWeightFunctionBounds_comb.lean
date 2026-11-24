-- Prove2me | Theorems.Thm_Formalism_G0_TopsWeightFunctionBounds_comb
-- name    : Formalism.G0.TopsWeightFunctionBounds.comb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:18.094808+00:00
-- url     : https://prove2.me/theorems/b5088e84-1306-4946-b1ec-f330f9d1c355
-- title:
--   Tops Weight Function Bounds: comb
-- statement:
--   The Tops Weight Function Bounds construction uses the comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L730-L792
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TopsChoicePartB.lean#L730-L792

import Definitions.Def_Formalism_SubspaceCounting_TopsChoiceSecondBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TopsChoicePartB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0 Formalism.G0.TopsWeightFunctionBounds

theorem Formalism.G0.TopsWeightFunctionBounds.comb {n : ℕ} (hn2 : 2 ≤ n) (hn : Even n) {L₂ r N₁ : ℕ} (hr : 1 ≤ r) (K₀ : ℕ)
    (hK : 1 + 3 * r * K₀ ≤ N₁) (T : Finset ℕ) (h : ¬ CondB n T L₂ r N₁) :
    ∃ i < n, i ∈ T ∧
      runS (3 * r) L₂ (init K₀ (decide (Even i))) ((Lst n i).map (fun p => decide (p ∈ T))) = .bad := by sorry
