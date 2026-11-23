-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_intPol_torsionFree
-- name    : Formalism.CountingSumsFrames.intPol_torsionFree
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:47:46.257054+00:00
-- url     : https://prove2.me/theorems/028afa7c-86d7-4126-9ce5-a012afbd0986
-- title:
--   Counting Sums Frames: int Pol torsion Free
-- statement:
--   The Counting Sums Frames construction uses the int Pol torsion Free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L113-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L113-L125

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
open Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.CountingSumsFrames.intPol_torsionFree {σ : Type} (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) : Module.IsTorsionFree ℤ_[p] L := by sorry
