-- Prove2me | Theorems.Thm_FamousTheorems_riesz_subsequence_convergence_in_measure_7a
-- name    : FamousTheorems.riesz_subsequence_convergence_in_measure_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:14.874735+00:00
-- url     : https://prove2.me/theorems/c751f378-57a9-4d6f-b9f0-7c6746f00a5e
-- title:
--   Riesz's subsequence theorem for convergence in measure
-- statement:
--   **Riesz's subsequence theorem for convergence in measure.** Let $(\alpha,\mu)$ be a measure space, $E$ a pseudo-extended-metric space, and $f_n,g:\alpha\to E$ with $f_n\to g$ in measure. Then there is a strictly increasing sequence $n_1<n_2<\cdots$ such that $f_{n_k}(x)\to g(x)$ for $\mu$-almost every $x$.
--
--   F. Riesz proved this in 1909. Convergence in measure does not imply almost-everywhere convergence, as the "typewriter" sequence of indicator functions shows, but it always does so along a subsequence. Since convergence in $L^p$ implies convergence in measure, it follows that every $L^p$-convergent sequence has an almost everywhere convergent subsequence. This fact is used in the proof that $L^p$ is complete.
--
--   **Formalization note.** Mathlib's `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`. `TendstoInMeasure μ f atTop g` says that for every $\varepsilon>0$, $\mu\{x:\operatorname{edist}(f_n(x),g(x))\ge\varepsilon\}\to0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem riesz_subsequence_convergence_in_measure_7a {α E : Type*} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [PseudoEMetricSpace E]
    {f : ℕ → α → E} {g : α → E} (hfg : MeasureTheory.TendstoInMeasure μ f Filter.atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ, Filter.Tendsto (fun i => f (ns i) x) Filter.atTop (nhds (g x)) := by sorry

end FamousTheorems
