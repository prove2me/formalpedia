-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_isoC_keep
-- name    : Formalism.CountingSumsFrames.isoC_keep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:53.286934+00:00
-- url     : https://prove2.me/theorems/1fec5b03-f2f4-4b52-9d43-fff04577a115
-- title:
--   Counting Sums Frames: iso C keep
-- statement:
--   The Counting Sums Frames construction uses the iso C keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1101-L1113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1101-L1113

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

theorem Formalism.CountingSumsFrames.isoC_keep (LL : Letters N) (j : ℕ) (la : Fin r → ℤ)
    (Q : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hc : ∀ c d x, Q (glAct p LL j c d x) = glAct p LL j c d (Q x))
    (hh : ∀ x ∈ HWC p LL j univ la, Q x ∈ HWC p LL j univ la) :
    ∀ x ∈ IsoC p LL j univ la, Q x ∈ IsoC p LL j univ la := by sorry
