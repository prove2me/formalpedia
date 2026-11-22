-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_comm_wtsp
-- name    : Formalism.CountingSumsFrames.comm_wtsp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:22.970996+00:00
-- url     : https://prove2.me/theorems/258eccec-9b3c-40a6-8379-0f82c3f3f86c
-- title:
--   Counting Sums Frames: comm wtsp
-- statement:
--   The Counting Sums Frames construction uses the comm wtsp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L798-L812
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L798-L812

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.comm_wtsp (LL : Letters N) (j : ℕ) (T : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hT : ∀ c x, T (glAct p LL j c c x) = glAct p LL j c c (T x)) (μ : Fin r → ℤ) :
    ∀ x ∈ WtSpC p LL j univ μ, T x ∈ WtSpC p LL j univ μ := by sorry
