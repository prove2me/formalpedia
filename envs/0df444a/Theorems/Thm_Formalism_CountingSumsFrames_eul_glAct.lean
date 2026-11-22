-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_eul_glAct
-- name    : Formalism.CountingSumsFrames.eul_glAct
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:26.930805+00:00
-- url     : https://prove2.me/theorems/560706e4-98f0-41c6-9b40-8f23e956b5b2
-- title:
--   Counting Sums Frames: eul gl Act
-- statement:
--   The Counting Sums Frames construction uses the eul gl Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1069-L1087
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1069-L1087

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

theorem Formalism.CountingSumsFrames.eul_glAct (LL : Letters N) (j : ℕ) (i0 : Fin N) (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ProjS.eulL (fun c : Fin r => (i0, c)) (glAct p LL j c d x) = glAct p LL j c d (ProjS.eulL (fun c : Fin r => (i0, c)) x) := by sorry
