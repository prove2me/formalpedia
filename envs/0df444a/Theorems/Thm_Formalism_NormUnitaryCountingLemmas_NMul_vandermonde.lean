-- Prove2me | Theorems.Thm_Formalism_NormUnitaryCountingLemmas_NMul_vandermonde
-- name    : Formalism.NormUnitaryCountingLemmas.NMul.vandermonde
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:17:50.554802+00:00
-- url     : https://prove2.me/theorems/260c2ffc-e7b3-41d8-9436-b21f1d9eea03
-- title:
--   NMul: vandermonde
-- statement:
--   The NMul construction uses the vandermonde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/NormUnitaryBounds/DetPolynomialWeights/NormMul.lean#L11-L23

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

theorem Formalism.NormUnitaryCountingLemmas.NMul.vandermonde {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℕ) (m : ℕ) :
    ∑ l ∈ finsuppAntidiag (univ : Finset ι) m, ∏ k, (c k).choose (l k) =
      (∑ k, c k).choose m := by sorry
