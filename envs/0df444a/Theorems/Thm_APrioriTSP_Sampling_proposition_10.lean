-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_proposition_10
-- name    : APrioriTSP.Sampling.proposition_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:21.890336+00:00
-- url     : https://prove2.me/theorems/70478451-8d02-4646-b7e8-7ed538107b4c
-- title:
--   Proposition 10, p. 8 — the expected cost of a tour from the depot on a p-normalized instance is Σ (1 − p)^{i−1} C_i
-- statement:
--   Let $(V, c, p)$ be a $p$-normalized instance ($p > 0$) with depot $d$: $p(d) = 1$ and every other customer is active with probability $p$. Let $T = (v_0, v_1, \dots, v_{n-1})$ be a tour with $v_0 = d$, put $v_j := v_0$ for $j < 0$ or $j > n-1$, and let $C_k = p^2 \sum_{j\in\mathbb Z} c(v_j, v_{j+k})$ for $k \ge 1$. Then the a priori cost of $T$ is
--   $$\mathbb E_{A\sim p}[c(T[A])] = \sum_{i=1}^\infty (1-p)^{i-1} C_i .$$
--
--   The proposition expresses the objective of the optimization problem (Sampling-OP) in the hop sums $C_k$, independently of the number of customers. Applied to an optimum tour $T^*$ it gives $\mathrm{OPT}$.
--
--   **Formalization Note** The series is a `tsum` with the index shift $i \mapsto i+1$; it converges, since $C_k$ is constant for $k \ge n$. At $p = 1$ only $C_1$, the tour length, survives.
--
--   Differences from the source:
--
--   - generalization: T* a fixed optimum a priori tour (p. 7) → every tour T whose first customer is the depot; reason: the identity does not use optimality; at T = T* it is the paper's statement
--   - encoding: C_k = p²·Σ_{j∈ℤ} c(v_j, v_{j+k}) → the sum over −k ≤ j ≤ n − 1; reason: the omitted summands are c(d, d) = 0
--   - encoding: Σ_{i=1}^∞ (1 − p)^{i−1} C_i → Σ_{i≥0} (1 − p)^i C_{i+1} as a `tsum`; reason: index shift; the series converges since C_k is constant for k ≥ n
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 8, Proposition 10, Equation (4)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- Proposition 10 (p. 8): on a `p`-normalized instance, the a priori cost of a tour starting
at the depot is `Σ_{i≥1} (1 − p)^{i−1} C_i` (index shifted `i ↦ i + 1`). -/
theorem proposition_10 {V : Type} [Fintype V] [DecidableEq V]
    (c : V → V → ℝ) (pf : V → ℝ) (d : V) (p : ℝ) (hp : 0 < p)
    (hnorm : IsNormalized c pf d p) (T : List V) (hT : IsTour T) (hd : T.head? = some d) :
    aPrioriCost c pf T = ∑' i : ℕ, (1 - p) ^ i * hopC c p d T (i + 1) := by sorry

end APrioriTSP.Sampling
