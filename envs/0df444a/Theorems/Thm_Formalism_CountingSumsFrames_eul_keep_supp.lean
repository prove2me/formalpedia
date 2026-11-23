-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_eul_keep_supp
-- name    : Formalism.CountingSumsFrames.eul_keep_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:54.576313+00:00
-- url     : https://prove2.me/theorems/dd3af35f-f5b8-43b9-be1c-0e6360f3bfa0
-- title:
--   Counting Sums Frames: eul keep supp
-- statement:
--   The Counting Sums Frames construction uses the eul keep supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1145-L1153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1145-L1153

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

theorem Formalism.CountingSumsFrames.eul_keep_supp {σ : Type} {s : ℕ} (t : Fin s → σ) (Q : Set (σ →₀ ℕ)) :
    ∀ x ∈ restrictSupport ℚ_[p] Q, ProjS.eulL t x ∈ restrictSupport ℚ_[p] Q := by sorry
