-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_glAct_keep
-- name    : Formalism.CountingSumsFrames.glAct_keep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:42.363699+00:00
-- url     : https://prove2.me/theorems/bc7bd3ed-6b72-4b1f-8537-74bbddbad780
-- title:
--   Counting Sums Frames: gl Act keep
-- statement:
--   The Counting Sums Frames construction uses the gl Act keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L646-L665
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L646-L665

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

theorem Formalism.CountingSumsFrames.glAct_keep (LL : Letters N) (j : ℕ) (c d : Fin r) (Q Q' : Set (Fin N × Fin r →₀ ℕ))
    (hv : ∀ i : Fin N, (i : ℕ) < j → LL.vec i = true → ∀ m ∈ Q, 1 ≤ m (i, d) →
      Finsupp.single (i, c) 1 + (m - Finsupp.single (i, d) 1) ∈ Q')
    (hc : ∀ i : Fin N, (i : ℕ) < j → LL.vec i = false → ∀ m ∈ Q, 1 ≤ m (i, c) →
      Finsupp.single (i, d) 1 + (m - Finsupp.single (i, c) 1) ∈ Q') :
    ∀ x ∈ restrictSupport ℚ_[p] Q, glAct p LL j c d x ∈ restrictSupport ℚ_[p] Q' := by sorry
