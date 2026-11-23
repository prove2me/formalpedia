-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_bweight_pos
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.bweight_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:43.992005+00:00
-- url     : https://prove2.me/theorems/9c97b681-c4f2-4721-92e6-2b14963a041e
-- title:
--   NMul: bweight pos
-- statement:
--   The NMul construction uses the bweight pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L44-L46

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

theorem Formalism.NormUnitaryCountingLemmas.NMul.bweight_pos {N n : ℕ} (e : Fin N × Fin n →₀ ℕ) : 0 < bweight e := by sorry
