-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_blockDeg_add
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.blockDeg_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:27.398665+00:00
-- url     : https://prove2.me/theorems/db9f55d4-ce2d-454f-b236-59fa814d03ed
-- title:
--   NMul: block Deg add
-- statement:
--   The NMul construction uses the block Deg add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L40-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L40-L42

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

theorem Formalism.NormUnitaryCountingLemmas.NMul.blockDeg_add {N n : ℕ} (a b : Fin N × Fin n →₀ ℕ) (j : Fin N) :
    blockDeg (a + b) j = blockDeg a j + blockDeg b j := by sorry
