-- Prove2me | Theorems.Thm_FD1D_FiniteLaw_timeAverage_mass
-- name    : FD1D.FiniteLaw.timeAverage_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:43:26.093899+00:00
-- url     : https://prove2.me/theorems/372c4a71-e864-4e90-b0aa-c3a2480d8615
-- title:
--   Finite Law: time Average mass
-- statement:
--   The Finite Law construction uses the time Average mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L35-L39
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Averaging.lean#L35-L39

import Definitions.Def_FD1D_Expectations
import Definitions.Def_FD1D_Averaging
set_option autoImplicit true
open FD1D
noncomputable section
open scoped BigOperators
open FD1D.FiniteLaw
variable {α : Type*} [Fintype α]

theorem FD1D.FiniteLaw.timeAverage_mass {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) (t : Fin T) (x : α) :
    (timeAverage hT μ).mass (t, x) =
      (1 / (T : ℝ)) * (μ t).mass x := by sorry

attribute [defeq] FD1D.FiniteLaw.timeAverage_mass
