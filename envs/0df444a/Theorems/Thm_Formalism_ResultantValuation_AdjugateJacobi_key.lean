-- Prove2me | Theorems.Thm_Formalism_ResultantValuation_AdjugateJacobi_key
-- name    : Formalism.ResultantValuation.AdjugateJacobi.key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:59.695801+00:00
-- url     : https://prove2.me/theorems/4d7232d9-ba61-416a-aed3-dc051acc8e88
-- title:
--   Adjugate Jacobi: key
-- statement:
--   The Adjugate Jacobi construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Adjugate.lean#L65-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ResultantValuation/ResultantAdjugateProofs/Adjugate.lean#L65-L77

import Definitions.Def_Formalism_ResultantValuation_KoszulSecondDifferential
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.AdjugateJacobi
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

theorem Formalism.ResultantValuation.AdjugateJacobi.key (M : Matrix n n R) {k i : n} (hki : k ≠ i) (l j : n) :
    M.det * minorF M k i l j = M.det * (M.det * minorQ M k i l j) := by sorry
