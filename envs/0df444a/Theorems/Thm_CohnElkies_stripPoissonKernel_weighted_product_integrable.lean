-- Prove2me | Theorems.Thm_CohnElkies_stripPoissonKernel_weighted_product_integrable
-- name    : CohnElkies.stripPoissonKernel_weighted_product_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:57:01.402116+00:00
-- url     : https://prove2.me/theorems/7340c3ee-e45e-419e-81a7-fb490eb2c3df
-- title:
--   CohnElkies.stripPoissonKernel_weighted_product_integrable
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | SpherePacking | external Lean 4.33.1 validation; bundle SHA256 ecca43e9570778e44777003bd5984d4ec94cd395fce5324c69b88ac50ad79ed2

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Metric Set
open scoped ENNReal Interval Topology

theorem CohnElkies.stripPoissonKernel_weighted_product_integrable
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {f : ℝ → ℝ} (hf : Integrable f) (s : ℝ) :
    Integrable (fun x : ℝ =>
      stripPoissonKernel σ (s - x) * f x) := by sorry
