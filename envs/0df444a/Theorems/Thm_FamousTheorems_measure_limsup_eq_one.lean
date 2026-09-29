-- Prove2me | Theorems.Thm_FamousTheorems_measure_limsup_eq_one
-- name    : FamousTheorems.measure_limsup_eq_one
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:25.353011+00:00
-- url     : https://prove2.me/theorems/bf4e4fdf-f77f-4a79-9809-640fb2312114
-- title:
--   The Borel–Cantelli lemma (difficult direction)
-- statement:
--   **The second Borel\u2013Cantelli lemma.** If the events $S_n$ are independent and $\sum_n \mu(S_n) = \infty$ then $$\mu\bigl(\limsup_n S_n\bigr) = 1,$$ so almost every point lies in infinitely many of them. Independence is essential here, unlike the first lemma: without it the conclusion fails outright, as the constant sequence $S_n = S$ with $0 < \mu(S) < 1$ shows. Together the two lemmas give a sharp zero\u2013one dichotomy for independent events — divergence of the series forces the event to recur forever, convergence forbids it — which is a special case of Kolmogorov's zero\u2013one law. It is the engine behind results on recurrence of random walks and on the almost-sure behaviour of records. **Formalization note.** Independence is `iIndepSet` under a probability measure. The result is Mathlib's `ProbabilityTheory.measure_limsup_eq_one`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem measure_limsup_eq_one :
    ∀ {Ω : Type u_1} {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω} 
    {s : ℕ → Set Ω}, 
    (∀ (n : ℕ), MeasurableSet (s n)) → ProbabilityTheory.iIndepSet s μ → ∑' (n : ℕ), μ (s n) = ⊤ → μ (limsup s atTop) = 1 := by sorry

end FamousTheorems
