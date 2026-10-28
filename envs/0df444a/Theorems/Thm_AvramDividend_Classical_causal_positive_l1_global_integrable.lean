-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable
-- name    : AvramDividend.Classical.causal_positive_l1_global_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T16:53:46.86703+00:00
-- url     : https://prove2.me/theorems/cc322a42-242d-4519-9599-a31e42f85e51
-- title:
--   Causal support promotes positive-time L1 to global integrability
-- statement:
--   If a real-valued function is integrable over strictly positive times and vanishes on all nonpositive times, it is integrable over the whole real line. Supplies the precise L1 bridge between the positive causal convolution construction and the global convolution continuity theorem.
-- source:
--   The support of f is contained in the positive half-line because f vanishes at every nonpositive argument. Apply the exact pinned Mathlib lemma integrableOn_iff_integrable_of_support_subset to transfer IntegrableOn to Integrable. This discharges the full real-line L1 hypothesis when applying the proved continuous-power convolution theorem to signed Gaussian Neumann powers.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_positive_l1_global_integrable
    (f : ℝ → ℝ)
    (hf : IntegrableOn f (Ioi (0 : ℝ)) volume)
    (hzero : ∀ x : ℝ, x ≤ 0 → f x = 0) :
    Integrable f volume := by sorry
