-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_lcomp_fock
-- name    : Formalism.CountingSumsFrames.lcomp_fock
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:11.57058+00:00
-- url     : https://prove2.me/theorems/9b36eb1b-e004-493c-9575-92a39e2a47f5
-- title:
--   Counting Sums Frames: lcomp fock
-- statement:
--   The Counting Sums Frames construction uses the lcomp fock property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1670-L1676
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1670-L1676

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

theorem Formalism.CountingSumsFrames.lcomp_fock {p : ℕ} [Fact p.Prime] {σ : Type} {ι : Type*} [LinearOrder ι]
    (P : ι → MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p])
    (hsa : ∀ j F G, fock p (P j F) G = fock p F (P j G)) (z : MvPolynomial σ ℚ_[p]) (hz : ∀ j, P j z = z) :
    ∀ l : List ι, ∀ u, fock p z (lcomp P l u) = fock p z u
  := by sorry
