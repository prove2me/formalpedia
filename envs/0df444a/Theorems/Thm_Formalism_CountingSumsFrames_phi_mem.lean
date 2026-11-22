-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_phi_mem
-- name    : Formalism.CountingSumsFrames.phi_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:46:48.210655+00:00
-- url     : https://prove2.me/theorems/87ed398a-211a-49ae-af2f-73f2a44973e6
-- title:
--   Counting Sums Frames: phi mem
-- statement:
--   The Counting Sums Frames construction uses the phi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L317-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L317-L332

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

theorem Formalism.CountingSumsFrames.phi_mem {N r : ℕ} [NeZero r] (LL : Letters N) (T : TieData) (j : Fin T.t) (h : T.pos j + 1 < N) :
    (T.phi p LL j : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])) ∈
      FockB.Ops {v : Fin N × Fin r | (v.1 : ℕ) = T.pos j ∨ (v.1 : ℕ) = T.pos j + 1} := by sorry
