-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_eul_XD
-- name    : Formalism.CountingSumsFrames.eul_XD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:46.724705+00:00
-- url     : https://prove2.me/theorems/4a7402ca-5c13-41ac-ad15-de9ba1324c80
-- title:
--   Counting Sums Frames: eul XD
-- statement:
--   The Counting Sums Frames construction uses the eul XD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1064-L1067
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1064-L1067

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

theorem Formalism.CountingSumsFrames.eul_XD {σ : Type} {s : ℕ} (t : Fin s → σ) (ht : Function.Injective t) (c d : Fin s)
    (g : MvPolynomial σ ℚ_[p]) :
    ProjS.eulL t (X (t c) * pderiv (t d) g) = X (t c) * pderiv (t d) (ProjS.eulL t g) := by sorry
