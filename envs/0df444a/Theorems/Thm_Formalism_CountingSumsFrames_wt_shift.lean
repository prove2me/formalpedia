-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_wt_shift
-- name    : Formalism.CountingSumsFrames.wt_shift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:51.099949+00:00
-- url     : https://prove2.me/theorems/a759989e-ceec-43d7-8296-db3c3f9bff6a
-- title:
--   Counting Sums Frames: wt shift
-- statement:
--   The Counting Sums Frames construction uses the wt shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L692-L719
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L692-L719

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

theorem Formalism.CountingSumsFrames.wt_shift (LL : Letters N) (j : ℕ) (c d c' : Fin r) (i : Fin N) (hi : (i : ℕ) < j)
    (m : Fin N × Fin r →₀ ℕ) :
    (LL.vec i = true → 1 ≤ m (i, d) → wt LL j c' (Finsupp.single (i, c) 1 + (m - Finsupp.single (i, d) 1) : Fin N × Fin r →₀ ℕ) =
      wt LL j c' m + (if c = c' then 1 else 0) - (if d = c' then 1 else 0)) ∧
    (LL.vec i = false → 1 ≤ m (i, c) → wt LL j c' (Finsupp.single (i, d) 1 + (m - Finsupp.single (i, c) 1) : Fin N × Fin r →₀ ℕ) =
      wt LL j c' m + (if c = c' then 1 else 0) - (if d = c' then 1 else 0)) := by sorry
