-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_integrable_mark_energy_tail_iInf_zero
-- name    : AvramDividend.Classical.avram_wave4_p1_integrable_mark_energy_tail_iInf_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T12:34:34.040324+00:00
-- url     : https://prove2.me/theorems/03134e86-e6de-49ec-8d59-26afc753df00
-- title:
--   Vanishing countable decreasing tails of integrable marked jump energy
-- statement:
--   For an arbitrary possibly infinite Lévy-type intensity measure ν on a measurable mark space, an integrable nonnegative mark energy f, and any decreasing sequence of measurable sets D_n with empty intersection, the infimum over n of ∫_{D_n}f dν is zero. The argument forms the finite weighted measure ρ=ν.withDensity f, uses continuity from above for its measurable shrinking sets, and identifies ρ(D_n) with the original weighted integrals. In particular, choosing f(z)=z² on small negative jumps yields the deterministic tail-energy vanishing that an independently proved compensated Poisson L² isometry needs to establish Cauchy convergence. No Poisson law, isometry or martingale assertion is assumed or concluded.
-- source:
--   Pinned Mathlib Measure.withDensity_apply, Antitone.measure_iInter; Lévy square intensity condition as in Applebaum, Lévy Processes and Stochastic Calculus, second edition.

import Mathlib

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_integrable_mark_energy_tail_iInf_zero
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) (f : E → ℝ≥0∞) (hf : Measurable f)
    (hfFinite : (∫⁻ z, f z ∂ν) ≠ ∞)
    (D : ℕ → Set E) (hDm : ∀ n, MeasurableSet (D n))
    (hDanti : Antitone D) (hDempty : (⋂ n, D n) = ∅) :
    (⨅ n, ∫⁻ z in D n, f z ∂ν) = 0 := by sorry
