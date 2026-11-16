-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_positive_event_limit_refutes_original_positive_error_ae
-- name    : AvramDividend.Classical.avram_bvb_obstruction_positive_event_limit_refutes_original_positive_error_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T00:57:31.192336+00:00
-- url     : https://prove2.me/theorems/97e8314e-51c2-4b7b-9d15-5cd429d5bc61
-- title:
--   Positive-probability limiting cash surplus refutes an almost-everywhere vanishing physical-grid error
-- statement:
--   On an event E of positive probability, if original stopped discounted cash F_n tends to a and original strict-internal drift ledger L_n tends to zero, where a exceeds candidate bound b, then the physical-grid positive error max(F_n-b-L_n,0) cannot vanish almost everywhere. This gives a source-ready logical contradiction for the original BV zero-mark drift-only leaf once the compound Poisson no-jump sample event is constructed.
-- source:
--   Apply the already Proved positive-part asymptotic contradiction pointwise on E, then the exact Mathlib ae_iff and measure monotonicity. The source F, L are arbitrary sequences, no hidden probabilistic assumptions; original compound-Poisson data will specialise them later.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_positive_cash_gap_excludes_zero_limit
open MeasureTheory Filter
open scoped Topology

theorem AvramDividend.Classical.avram_bvb_obstruction_positive_event_limit_refutes_original_positive_error_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (hE : 0 < P E)
    (F L : ℕ → Ω → ℝ) (b a : ℝ) (hgap : b < a)
    (hF : ∀ ω ∈ E, Tendsto (fun n => F n ω) atTop (𝓝 a))
    (hL : ∀ ω ∈ E, Tendsto (fun n => L n ω) atTop (𝓝 (0 : ℝ))) :
    ¬ (∀ᵐ ω ∂P,
        Tendsto (fun n => max (F n ω - (b + L n ω)) 0)
          atTop (𝓝 (0 : ℝ))) := by sorry
