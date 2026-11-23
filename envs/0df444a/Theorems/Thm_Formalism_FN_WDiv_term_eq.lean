-- Prove2me | Theorems.Thm_Formalism_FN_WDiv_term_eq
-- name    : Formalism.FN.WDiv.term_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:40.564629+00:00
-- url     : https://prove2.me/theorems/7964fde5-8148-4381-aa94-17afeab852e6
-- title:
--   WDiv: term eq
-- statement:
--   The WDiv construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPWDivision.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPWDivision.lean#L13-L17

import Definitions.Def_Formalism_SuccessiveMinima_DefsNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
noncomputable section
open Formalism Formalism.FN Formalism.FN.WDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem Formalism.FN.WDiv.term_eq (a b : ℕ → K) (r : ℝ) {n i : ℕ} (hi : i ≤ n) :
    ‖a i * b (n - i)‖ * r ^ n = (‖a i‖ * r ^ i) * (‖b (n - i)‖ * r ^ (n - i)) := by sorry
