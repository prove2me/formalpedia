-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_normSq_mul
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.normSq_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:55.739813+00:00
-- url     : https://prove2.me/theorems/6cf0ed60-434f-4a5a-997d-157af115f951
-- title:
--   NMul: norm Sq mul
-- statement:
--   The NMul construction uses the norm Sq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L218-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L218-L240

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

theorem Formalism.NormUnitaryCountingLemmas.NMul.normSq_mul {N n : ℕ} (ν : Fin N → ℕ) (F G : MvPolynomial (Fin N × Fin n) ℂ)
    (hF : F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν) :
    bnormSq (F * G) ≤ bnormSq F * bnormSq G := by sorry
