-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ycond_keep
-- name    : Formalism.CountingSumsFrames.ycond_keep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:57.383614+00:00
-- url     : https://prove2.me/theorems/20b2879c-3dac-48df-a32d-f1505e5fac37
-- title:
--   Counting Sums Frames: ycond keep
-- statement:
--   The Counting Sums Frames construction uses the ycond keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L417-L441
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L417-L441

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
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.CountingSumsFrames.ycond_keep {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (T : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, T (glAct p LL j c d x) = glAct p LL j c d (T x))
    (hw : ∀ x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt},
      T x ∈ restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt}) :
    ∀ x ∈ YCond p (r := r) LL j Mt, T x ∈ YCond p (r := r) LL j Mt := by sorry
