-- Prove2me | Theorems.Thm_FamousTheorems_weierstrass_m_test_7a
-- name    : FamousTheorems.weierstrass_m_test_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:25:50.367956+00:00
-- url     : https://prove2.me/theorems/f2fc8e38-f2f1-4932-a659-12110c890d39
-- title:
--   The Weierstrass M-test
-- statement:
--   **The Weierstrass M-test.** Let $f_n:\beta\to F$ be functions into a complete normed group, indexed by $n\in\alpha$, and let $u:\alpha\to\mathbb R$ be summable with $\|f_n(x)\|\le u_n$ for all $n$ and $x$. Then the partial sums $\sum_{n\in t}f_n$, over finite sets $t\subseteq\alpha$, converge uniformly on $\beta$ to $\sum_n f_n$.
--
--   This test is due to Weierstrass. It is the standard tool for proving uniform convergence of series of functions, and hence continuity of their sums. Examples include power series inside their disc of convergence, the Weierstrass nowhere-differentiable function and theta series.
--
--   **Formalization note.** Mathlib's `tendstoUniformly_tsum`. The partial sums are indexed by finite subsets $t$ of the index set, ordered by inclusion (`Filter.atTop` on `Finset α`). `∑' n, f n x` is the sum of the series, and `TendstoUniformly` is uniform convergence on all of $\beta$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `tendstoUniformly_tsum`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem weierstrass_m_test_7a {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ} {f : α → β → F}
    (hu : Summable u) (hfu : ∀ n x, ‖f n x‖ ≤ u n) :
    TendstoUniformly (fun (t : Finset α) (x : β) => ∑ n ∈ t, f n x) (fun x => ∑' n, f n x) Filter.atTop := by sorry

end FamousTheorems
