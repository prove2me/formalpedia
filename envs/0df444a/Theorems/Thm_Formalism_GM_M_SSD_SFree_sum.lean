-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_SFree_sum
-- name    : Formalism.GM.M.SSD.SFree.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:23.982135+00:00
-- url     : https://prove2.me/theorems/76c090a8-ee8c-4bc9-88fb-13e200db6f27
-- title:
--   SFree: sum
-- statement:
--   The SFree construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L127-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L127-L134

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

theorem Formalism.GM.M.SSD.SFree.sum {α : Type} (u : Finset α) (f : α → MvPolynomial σ K) (h : ∀ i ∈ u, SFree sv (f i)) :
    SFree sv (∑ i ∈ u, f i) := by sorry
