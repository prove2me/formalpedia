-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_lcomp_int
-- name    : Formalism.CountingSumsFrames.lcomp_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:24:16.7736+00:00
-- url     : https://prove2.me/theorems/73e6f18f-b5fb-4121-9daf-76fccc7fdf08
-- title:
--   Counting Sums Frames: lcomp int
-- statement:
--   The Counting Sums Frames construction uses the lcomp int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1678-L1692
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1678-L1692

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

theorem Formalism.CountingSumsFrames.lcomp_int {p : ℕ} [Fact p.Prime] {N r : ℕ} {ι : Type*} [LinearOrder ι] (LL : Letters N) (e1 : ℕ)
    (P : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hpol : ∀ j, ∀ x ∈ Pol p r LL, P j x ∈ Pol p r LL)
    (hint : ∀ j, ∀ F ∈ PolZ p r LL, ((p : ℚ_[p]) ^ e1) • P j F ∈ IntPol p (Fin N × Fin r)) :
    ∀ l : List ι, ∀ u ∈ PolZ p r LL, ((p : ℚ_[p]) ^ (e1 * l.length)) • lcomp P l u ∈ PolZ p r LL
  := by sorry
