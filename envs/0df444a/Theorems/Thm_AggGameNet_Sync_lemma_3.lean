-- Prove2me | Theorems.Thm_AggGameNet_Sync_lemma_3
-- name    : AggGameNet.Sync.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:15.220252+00:00
-- url     : https://prove2.me/theorems/71be0ace-b2e2-448e-84ae-b81d0b8b73d8
-- title:
--   Lemma 3, p. 10 — bounded gradient evaluations along the synchronous run
-- statement:
--   Consider the synchronous algorithm on nonempty compact convex strategy sets, with continuous $F_i$, positive uniformly Lipschitz constants $\bar L_i$ in the aggregate argument, connected graph windows, and neighbour-supported doubly stochastic weights bounded below by $\delta>0$. There is a single finite constant $C$ such that, for every player $i$ and time $k\ge0$,
--
--   $$\|F_i(x_i^k,Ny^k)\|\le C,\qquad\|F_i(x_i^k,N\hat v_i^k)\|\le C.$$
--
--   This supplies the uniform bound used in the disagreement and convergence estimates.
--
--   **Formalization Note** The printed Lemma 3 assumes only unit column sums, which permits unbounded weights. This statement includes Assumptions 4–5 and extends Assumption 3 to all aggregate arguments, since the algorithm evaluates $F_i$ outside $\bar K$.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, Lemma 3, p. 10; corrected domain and weight conditions explained in paper.md Printed gaps 1–2

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting

namespace AggGameNet.Sync

/-- Lemma 3, p. 10, with the pinned mixing and Lipschitz hypotheses. -/
theorem lemma_3 {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F) (Lbar : Fin N → ℝ)
    (h3 : Assumption3 K F Lbar)
    (G : ℕ → SimpleGraph (Fin N)) (Q : ℕ) (h4 : Assumption4 G Q)
    (W : ℕ → Matrix (Fin N) (Fin N) ℝ) (δ : ℝ)
    (hδ : 0 < δ) (h5 : Assumption5 G W δ)
    (α : ℕ → ℝ) (x v : ℕ → Fin N → E n)
    (hrun : IsSyncRun K F W α x v) :
    ∃ C : ℝ, ∀ i k,
      ‖F i (x k i) ((N : ℝ) • yavg v k)‖ ≤ C ∧
      ‖F i (x k i) ((N : ℝ) • vhat W v k i)‖ ≤ C := by sorry

end AggGameNet.Sync
