-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_SFree_prod
-- name    : Formalism.GM.M.SSD.SFree.prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:17.022797+00:00
-- url     : https://prove2.me/theorems/99fbf6b3-9f79-4e08-ac27-f3ea05026a3c
-- title:
--   SFree: prod
-- statement:
--   The SFree construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L137-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L137-L144

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
omit [Nontrivial K]

theorem Formalism.GM.M.SSD.SFree.prod {α : Type} (u : Finset α) (f : α → MvPolynomial σ K) (h : ∀ i ∈ u, SFree sv (f i)) :
    SFree sv (∏ i ∈ u, f i) := by sorry
