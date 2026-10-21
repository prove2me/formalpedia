-- Prove2me | Theorems.Thm_AVHighway_DPolicy_lemma_1
-- name    : AVHighway.DPolicy.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:08.972914+00:00
-- url     : https://prove2.me/theorems/3ad97c45-5fd5-42f8-8abd-964efba106f6
-- title:
--   Lemma 1, Online Appendix p. 4 — the mean travel time W of an M/G_n/c/c queue is increasing in λ
-- statement:
--   Consider the $M/G_n/c/c$ loss queue with segment length $L > 0$, capacity $c \ge 1$, and speeds $V_1 \ge V_2 \ge \dots \ge V_c > 0$ (speed decreases with the number of vehicles, the standing assumption of §3.1.1). Let $W(\lambda)$ be its mean travel time (13) at arrival rate $\lambda$. Then $W$ is (weakly) increasing in the arrival rate:
--   $$0 < \lambda \le \lambda' \implies W(\lambda) \le W(\lambda').$$
--
--   Lemma 1 is what makes the paper's comparison between policies a statement about heavy load: as traffic grows, travel times only get worse, and they approach the jam-speed limits of display (20).
--
--   **Formalization Note** "Increasing" is read weakly: with nonincreasing speeds $W$ can be constant (constant speeds give $W \equiv L/V_1$). The paper states the lemma for $\lambda \ge 0$; here $\lambda > 0$, because at $\lambda = 0$ the throughput vanishes and Lean's $x/0 = 0$ assigns $W = 0$ instead of the paper's limiting value $L/V_1$.
-- source:
--   Mirzaeian, Cho & Scheller-Wolf, A Queueing Model and Analysis for Autonomous Vehicles on Highways, SSRN 3278330 (version of May 5, 2020; Manag. Sci. doi:10.1287/mnsc.2020.3692), Lemma 1, Online Appendix p. 4; standing assumption 'V_n is decreasing in n', §3.1.1, p. 7

import Mathlib
import Definitions.Def_AVHighway_DPolicy_LossQueue

namespace AVHighway.DPolicy
theorem lemma_1 (L : ℝ) (hL : 0 < L) (V : ℕ → ℝ) (cap : ℕ) (hcap : 1 ≤ cap)
    (hV : ∀ n, 1 ≤ n → n ≤ cap → 0 < V n) (hVanti : AntitoneOn V (Set.Icc 1 cap)) :
    MonotoneOn (meanTravelTime L V cap) (Set.Ioi 0) := by sorry
end AVHighway.DPolicy
