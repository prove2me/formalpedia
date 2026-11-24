-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_euler_eq_dg
-- name    : Formalism.MainNotions.PlaneGram.euler_eq_dg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:06:52.891794+00:00
-- url     : https://prove2.me/theorems/a8d084e6-6749-43f4-a874-a11e6bdc1611
-- title:
--   Plane Gram: euler eq dg
-- statement:
--   The Plane Gram construction uses the euler eq dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ProjKeepsLetter.lean#L120-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ProjKeepsLetter.lean#L120-L124

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
variable {L : Type} [DecidableEq L] (sg : L → Bool) {r : ℕ}

theorem Formalism.MainNotions.PlaneGram.euler_eq_dg {σ : Type} (x : σ) (G : MvPolynomial σ K) :
    X x * pderiv x G = dg (fun ξ => (ξ x : K)) G := by sorry
