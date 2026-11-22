-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_fock_monomial
-- name    : Formalism.CountingSumsFrames.fock_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:47:02.468775+00:00
-- url     : https://prove2.me/theorems/395bbe03-6866-499b-8a09-67a918272861
-- title:
--   Counting Sums Frames: fock monomial
-- statement:
--   The Counting Sums Frames construction uses the fock monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1605-L1612
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/PartnerM.lean#L1605-L1612

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

theorem Formalism.CountingSumsFrames.fock_monomial {σ : Type} (z : MvPolynomial σ ℚ_[p]) (m0 : σ →₀ ℕ) (hm0 : m0 ∈ z.support) :
    fock p z (monomial m0 1) = coeff m0 z * (m0.prod fun _ k => (k.factorial : ℚ_[p])) := by sorry
