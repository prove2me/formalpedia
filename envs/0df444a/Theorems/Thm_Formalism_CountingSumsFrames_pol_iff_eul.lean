-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_pol_iff_eul
-- name    : Formalism.CountingSumsFrames.pol_iff_eul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:00.798952+00:00
-- url     : https://prove2.me/theorems/f5c3f1df-8f22-412b-99cf-1b11c536aefd
-- title:
--   Counting Sums Frames: pol iff eul
-- statement:
--   The Counting Sums Frames construction uses the pol iff eul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L334-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L334-L346

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

theorem Formalism.CountingSumsFrames.pol_iff_eul {N r : ℕ} (LL : Letters N) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    x ∈ Pol p r LL ↔ ∀ i : Fin N, ProjS.eulL (fun c : Fin r => (i, c)) x = ((LL.deg i : ℕ) : ℚ_[p]) • x := by sorry
