-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_weight_blockWt
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.weight_blockWt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:50.473854+00:00
-- url     : https://prove2.me/theorems/e6a67792-922c-4068-b816-157354c7060e
-- title:
--   NMul: weight block Wt
-- statement:
--   The NMul construction uses the weight block Wt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L25-L31

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

theorem Formalism.NormUnitaryCountingLemmas.NMul.weight_blockWt {N n : ℕ} (a : Fin N × Fin n →₀ ℕ) (j : Fin N) :
    Finsupp.weight (blockWt N n) a j = blockDeg a j := by sorry
