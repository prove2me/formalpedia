-- Prove2me | Theorems.Thm_FamousTheorems_kolmogorov_zero_one_law
-- name    : FamousTheorems.kolmogorov_zero_one_law
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:25:53.450305+00:00
-- url     : https://prove2.me/theorems/a4e103eb-d904-4cf4-b7b4-da1333ffab0c
-- title:
--   Kolmogorov's 0-1 law
-- statement:
--   **Kolmogorov's 0-1 law.** Let $(s_n)_{n\in\mathbb N}$ be a sequence of independent sub-σ-algebras on a probability space $(\Omega,\mu)$. Every event $t$ in the tail σ-algebra
--   $$\mathcal T=\bigcap_{n}\sigma\Big(\bigcup_{i\ge n}s_i\Big)$$
--   has probability $0$ or $1$.
--
--   For instance, for independent random variables $X_n$, the convergence of $\sum X_n$ and the event $\limsup X_n>c$ are tail events and so are almost sure or almost impossible. The law is a basic tool of probability theory, used for example in the Borel–Cantelli lemmas and the strong law of large numbers.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop`. The tail σ-algebra is `Filter.limsup s Filter.atTop` in the complete lattice of σ-algebras, which equals the intersection above. `ProbabilityTheory.iIndep s μ` is mutual independence and already forces `μ` to be a probability measure.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.measure_zero_or_one_of_measurableSet_limsup_atTop`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open scoped MeasureTheory

theorem kolmogorov_zero_one_law {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} (s : ℕ → MeasurableSpace Ω)
    (h_le : ∀ n, s n ≤ m0) (h_indep : ProbabilityTheory.iIndep s μ) {t : Set Ω}
    (ht_tail : MeasurableSet[Filter.limsup s Filter.atTop] t) : μ t = 0 ∨ μ t = 1 := by sorry

end FamousTheorems
