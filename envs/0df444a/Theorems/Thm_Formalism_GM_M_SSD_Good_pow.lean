-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_Good_pow
-- name    : Formalism.GM.M.SSD.Good.pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:45:05.724468+00:00
-- url     : https://prove2.me/theorems/cc029810-dc3f-40a4-b259-cfaf9c5867a2
-- title:
--   Good: pow
-- statement:
--   The Good construction uses the pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L82-L86

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

theorem Formalism.GM.M.SSD.Good.pow {f : MvPolynomial σ K} {a : ι → ℕ} {s : σ →₀ ℕ} (hf : Good sv f a s) (n : ℕ) :
    Good sv (f ^ n) (n • a) (n • s) := by sorry
