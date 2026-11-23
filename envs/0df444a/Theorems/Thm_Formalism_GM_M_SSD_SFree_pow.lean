-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_SFree_pow
-- name    : Formalism.GM.M.SSD.SFree.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:13.608983+00:00
-- url     : https://prove2.me/theorems/ad7317ae-433a-4ec8-b5f4-15bc6af76aaf
-- title:
--   SFree: pow
-- statement:
--   The SFree construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L147-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L147-L150

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

theorem Formalism.GM.M.SSD.SFree.pow {f : MvPolynomial σ K} (hf : SFree sv f) (n : ℕ) : SFree sv (f ^ n) := by sorry
