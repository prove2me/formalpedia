-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_tm_mem
-- name    : Formalism.CountingSumsFrames.tm_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:26.508617+00:00
-- url     : https://prove2.me/theorems/ac9d14b6-8bdc-4a50-a491-6d5c33a58f61
-- title:
--   Counting Sums Frames: tm mem
-- statement:
--   The Counting Sums Frames construction uses the tm mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L926-L942
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L926-L942

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

theorem Formalism.CountingSumsFrames.tm_mem (LL : Letters N) (j : ℕ) (i : Fin N) (c d : Fin r) :
    tm (p := p) LL j i c d ∈ FockB.Ops {v : Fin N × Fin r | v.1 = i} := by sorry
