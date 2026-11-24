-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_Good_mul_sfree
-- name    : Formalism.GM.M.SSD.Good.mul_sfree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:09.91783+00:00
-- url     : https://prove2.me/theorems/7878c784-8903-4843-9f49-7224824d98ff
-- title:
--   Good: mul sfree
-- statement:
--   The Good construction uses the mul sfree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L159-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L159-L189

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ ι K : Type} [CommRing K] [Nontrivial K] [DecidableEq σ] (sv : ι → σ)

theorem Formalism.GM.M.SSD.Good.mul_sfree {f Q : MvPolynomial σ K} {a : ι → ℕ} {s : σ →₀ ℕ} (hf : Good sv f a s)
    (hQ : SFree sv Q) :
    (∀ m ∈ (f * Q).support, sd sv m ≤ a) ∧ (∀ n, coeff (s + n) (f * Q) = coeff n Q) := by sorry
