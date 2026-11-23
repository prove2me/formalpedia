-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_tm_comm_ne
-- name    : Formalism.CountingSumsFrames.tm_comm_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:53:21.457264+00:00
-- url     : https://prove2.me/theorems/98ce4a5d-c7b7-43db-846b-f3de7010afab
-- title:
--   Counting Sums Frames: tm comm ne
-- statement:
--   The Counting Sums Frames construction uses the tm comm ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L944-L972
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L944-L972

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

theorem Formalism.CountingSumsFrames.tm_comm_ne (LL : Letters N) (j : ℕ) (i i' : Fin N) (hii : i ≠ i') (c d a b : Fin r)
    (y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    tm (p := p) LL j i c d (tm (p := p) LL j i' a b y) = tm (p := p) LL j i' a b (tm (p := p) LL j i c d y) := by sorry
