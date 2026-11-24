-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_bweight_add
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.bweight_add
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:43.564846+00:00
-- url     : https://prove2.me/theorems/4d72a55e-796c-418b-b6ce-62db2dd98c97
-- title:
--   NMul: bweight add
-- statement:
--   The NMul construction uses the bweight add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L53-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L53-L69

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_NormMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finset
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open Formalism.NormUnitaryCountingLemmas.NMul

theorem Formalism.NormUnitaryCountingLemmas.NMul.bweight_add {N n : ℕ} (a b : Fin N × Fin n →₀ ℕ) :
    bweight (a + b) * ∏ j, ((blockDeg (a + b) j).choose (blockDeg a j) : ℝ) =
      bweight a * bweight b * ∏ j, ∏ k, (((a + b) (j, k)).choose (a (j, k)) : ℝ) := by sorry
