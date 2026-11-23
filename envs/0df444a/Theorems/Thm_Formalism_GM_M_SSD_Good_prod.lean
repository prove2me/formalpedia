-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_Good_prod
-- name    : Formalism.GM.M.SSD.Good.prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:59.564106+00:00
-- url     : https://prove2.me/theorems/222b068a-a6ef-4754-a281-5ca8de72427e
-- title:
--   Good: prod
-- statement:
--   The Good construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L88-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L88-L96

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

theorem Formalism.GM.M.SSD.Good.prod {α : Type} (u : Finset α) (f : α → MvPolynomial σ K) (a : α → ι → ℕ) (s : α → σ →₀ ℕ)
    (h : ∀ i ∈ u, Good sv (f i) (a i) (s i)) :
    Good sv (∏ i ∈ u, f i) (∑ i ∈ u, a i) (∑ i ∈ u, s i) := by sorry
