-- Prove2me | Theorems.Thm_FamousTheorems_monotone_convergence_bounded_7b
-- name    : FamousTheorems.monotone_convergence_bounded_7b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:34:53.733989+00:00
-- url     : https://prove2.me/theorems/e7d09e3e-df8b-4d44-bea2-78dddf7e16f6
-- title:
--   Monotone convergence theorem for bounded sequences
-- statement:
--   **Monotone convergence theorem for sequences.** Let $(a_n)$ be a nondecreasing sequence of real numbers that is bounded above. Then $(a_n)$ converges, and its limit is $\sup_n a_n$.
--
--   This is one of the first convergence tests in analysis. It is used to define $e=\lim(1+1/n)^n$ and infinite decimal expansions, to prove convergence of series with nonnegative terms, and in the construction of the Lebesgue integral. It is equivalent to the least upper bound property of $\mathbb R$.
--
--   **Formalization note.** Mathlib's `tendsto_atTop_ciSup`, specialized to real sequences. `⨆ i, f i` is the supremum of the values of $f$, and `Filter.Tendsto f Filter.atTop (nhds L)` says that $f(n)\to L$ as $n\to\infty$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `tendsto_atTop_ciSup`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem monotone_convergence_bounded_7b {f : ℕ → ℝ} (hf : Monotone f) (hbdd : BddAbove (Set.range f)) :
    Filter.Tendsto f Filter.atTop (nhds (⨆ i, f i)) := by sorry

end FamousTheorems
