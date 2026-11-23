-- Prove2me | Theorems.Thm_Formalism_FX_rpow_eq_prod_primeFactors
-- name    : Formalism.FX.rpow_eq_prod_primeFactors
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:43:14.339063+00:00
-- url     : https://prove2.me/theorems/c17efc17-bbca-41ed-872d-f0146757095f
-- title:
--   FX: rpow eq prod prime Factors
-- statement:
--   The FX construction uses the rpow eq prod prime Factors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean#L45-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LFunctionBounds/LFunctionBoundsProofs/DivisorBound.lean#L45-L54

import Definitions.Def_Formalism_LFunctionBounds_PositivityBound
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_DivisorBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FX
open Finset

theorem Formalism.FX.rpow_eq_prod_primeFactors (e : ℝ) {n : ℕ} (hn0 : n ≠ 0) :
    (n : ℝ) ^ e = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ e) ^ (n.factorization p) := by sorry
