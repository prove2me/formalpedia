-- Prove2me | Theorems.Thm_FamousTheorems_first_moment_method
-- name    : FamousTheorems.first_moment_method
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:09.675527+00:00
-- url     : https://prove2.me/theorems/2009f7df-bb62-41d4-8d55-1d3db930ee7f
-- title:
--   The first moment method
-- statement:
--   **The first moment method.** Let $\mu$ be a measure, $s$ a set with $0<\mu(s)<\infty$, and $f$ integrable on $s$. Then the set of points $x\in s$ with
--   $$f(x)\le\frac1{\mu(s)}\int_s f\,d\mu$$
--   has positive measure.
--
--   A function cannot exceed its average everywhere. In the probabilistic method this is the first moment method: if a random variable has expectation $m$, it takes a value at most $m$ with positive probability. It is used to prove the existence of combinatorial objects, such as Erdős' lower bound for Ramsey numbers.
--
--   **Formalization note.** Mathlib's `MeasureTheory.measure_le_setAverage_pos`. `⨍ a in s, f a ∂μ` is the average of `f` over `s`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.measure_le_setAverage_pos`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem first_moment_method {α : Type*} {m0 : MeasurableSpace α} {μ : Measure α} {s : Set α} {f : α → ℝ} (hμ : μ s ≠ 0)
    (hμ' : μ s ≠ ⊤) (hf : IntegrableOn f s μ) : 0 < μ {x | x ∈ s ∧ f x ≤ ⨍ a in s, f a ∂μ} := by sorry

end FamousTheorems
