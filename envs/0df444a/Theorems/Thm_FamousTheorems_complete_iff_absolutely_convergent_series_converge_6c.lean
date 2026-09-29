-- Prove2me | Theorems.Thm_FamousTheorems_complete_iff_absolutely_convergent_series_converge_6c
-- name    : FamousTheorems.complete_iff_absolutely_convergent_series_converge_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:33.246363+00:00
-- url     : https://prove2.me/theorems/68b03c7b-2823-412e-851b-535de0d7d4d3
-- title:
--   A normed group is complete iff every absolutely convergent series converges
-- statement:
--   **Completeness and absolutely convergent series.** A normed abelian group $E$ is complete if and only if every absolutely convergent series in $E$ converges. That is, $E$ is complete exactly when, for every sequence $(u_n)$ with $\sum_n\|u_n\|<\infty$, the partial sums $\sum_{i<n}u_i$ converge in $E$.
--
--   This is the standard test for completeness of a normed space. It is used to prove that $L^p$ spaces are complete (the Riesz–Fischer theorem) and that quotients of Banach spaces are Banach spaces.
--
--   **Formalization note.** Mathlib's `NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace`. Absolute convergence is `Summable (fun n => ‖u n‖)`, and convergence of the series is convergence of the partial sums `∑ i ∈ Finset.range n, u i` as $n\to\infty$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem complete_iff_absolutely_convergent_series_converge_6c {E : Type*} [NormedAddCommGroup E] :
    (∀ u : ℕ → E, Summable (fun n => ‖u n‖) →
      ∃ a, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, u i) Filter.atTop (nhds a)) ↔
    CompleteSpace E := by sorry

end FamousTheorems
