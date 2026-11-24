-- Prove2me | Theorems.Thm_Formalism_GM_M_SSD_absDirect
-- name    : Formalism.GM.M.SSD.absDirect
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:15.198303+00:00
-- url     : https://prove2.me/theorems/397499d9-8b5b-43a5-b8d7-3ff5960191d8
-- title:
--   SSD: abs Direct
-- statement:
--   The SSD construction uses the abs Direct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L220-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L220-L244

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

theorem Formalism.GM.M.SSD.absDirect (V : ι' → Submodule K (MvPolynomial σ K)) (a : ι' → ι → ℕ) (ha : Function.Injective a)
    (h1 : ∀ L, ∀ v ∈ V L, ∀ m ∈ v.support, sd sv m ≤ a L)
    (h2 : ∀ L, ∀ v ∈ V L, (∀ m, sd sv m = a L → coeff m v = 0) → v = 0) : iSupIndep V := by sorry
