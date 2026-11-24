-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_eq_of_le_sum
-- name    : Formalism.GM.M.SSD.eq_of_le_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:30.215836+00:00
-- url     : https://prove2.me/theorems/b25ee946-5276-4da0-b99a-c8601f9fdb58
-- title:
--   SSD: eq of le sum
-- statement:
--   The SSD construction uses the eq of le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L202-L205

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
variable {σ ι K ι' : Type} [Field K] [DecidableEq σ] [Fintype ι] (sv : ι → σ)

theorem Formalism.GM.M.SSD.eq_of_le_sum {x y : ι → ℕ} (h : x ≤ y) (hs : ∑ k, y k ≤ ∑ k, x k) : x = y := by sorry
