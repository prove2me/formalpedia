-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ycond_glStable
-- name    : Formalism.CountingSumsFrames.ycond_glStable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:21.213619+00:00
-- url     : https://prove2.me/theorems/58280cbf-64fe-4ab9-96b3-a9b70bd0facd
-- title:
--   Counting Sums Frames: ycond gl Stable
-- statement:
--   The Counting Sums Frames construction uses the ycond gl Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1185-L1195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1185-L1195

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

theorem Formalism.CountingSumsFrames.ycond_glStable [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) (c d : Fin r) :
    ∀ x ∈ YCond p (r := r) LL j Mt, glAct p LL j c d x ∈ YCond p (r := r) LL j Mt := by sorry
