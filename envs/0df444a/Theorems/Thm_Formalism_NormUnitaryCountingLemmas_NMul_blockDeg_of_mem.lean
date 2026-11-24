-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_blockDeg_of_mem
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.blockDeg_of_mem
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T10:16:39.910078+00:00
-- url     : https://prove2.me/theorems/65d05a36-4d7b-4d36-8c44-28606cfd7019
-- title:
--   NMul: block Deg of mem
-- statement:
--   The NMul construction uses the block Deg of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L33-L38

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

theorem Formalism.NormUnitaryCountingLemmas.NMul.blockDeg_of_mem {N n : ℕ} {ν : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin n) ℂ}
    (hF : F ∈ weightedHomogeneousSubmodule ℂ (blockWt N n) ν) {a : Fin N × Fin n →₀ ℕ}
    (ha : a ∈ F.support) (j : Fin N) : blockDeg a j = ν j := by sorry
