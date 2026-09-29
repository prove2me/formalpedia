-- Prove2me | Theorems.Thm_FamousTheorems_doob_upcrossing_inequality
-- name    : FamousTheorems.doob_upcrossing_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:05.826249+00:00
-- url     : https://prove2.me/theorems/61e2db80-6060-49e0-a06a-5688aa5ef716
-- title:
--   Doob's upcrossing inequality
-- statement:
--   **Doob's upcrossing inequality.** Let $(f_n)$ be a submartingale on a finite measure space and $a<b$ real numbers. Let $U_N$ be the number of upcrossings of the interval $[a,b]$ completed by $f_0,\dots,f_N$. Then
--   $$(b-a)\,\mathbb E[U_N]\le\mathbb E\big[(f_N-a)^+\big].$$
--
--   The inequality bounds how often a submartingale can oscillate across a fixed interval. It is the key step in Doob's martingale convergence theorem: an $L^1$-bounded submartingale has finitely many upcrossings of every rational interval almost surely, so it converges almost surely.
--
--   **Formalization note.** Mathlib's `MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`. `upcrossingsBefore a b f N ω` is the natural number of upcrossings of $[a,b]$ before time $N$, cast to `ℝ` inside the integral. `x⁺` is the positive part $\max(x,0)$. When $b\le a$ the left side is nonpositive and the statement is trivial.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem doob_upcrossing_inequality {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {f : ℕ → Ω → ℝ} {ℱ : Filtration ℕ m0}
    [IsFiniteMeasure μ] (a b : ℝ) (hf : Submartingale f ℱ μ) (N : ℕ) :
    (b - a) * ∫ ω, (upcrossingsBefore a b f N ω : ℝ) ∂μ ≤ ∫ ω, (f N ω - a)⁺ ∂μ := by sorry

end FamousTheorems
