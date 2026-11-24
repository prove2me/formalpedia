-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_fact_add
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.fact_add
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:31.18291+00:00
-- url     : https://prove2.me/theorems/0e1ce59a-2489-45da-b4d0-c2fb471ace1d
-- title:
--   NMul: fact add
-- statement:
--   The NMul construction uses the fact add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L48-L51

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

theorem Formalism.NormUnitaryCountingLemmas.NMul.fact_add (x y : ℕ) :
    ((x + y).factorial : ℝ) = ((x + y).choose x : ℝ) * x.factorial * y.factorial := by sorry
