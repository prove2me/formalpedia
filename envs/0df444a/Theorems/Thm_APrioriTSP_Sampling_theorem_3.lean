-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_theorem_3
-- name    : APrioriTSP.Sampling.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:38:43.520562+00:00
-- url     : https://prove2.me/theorems/6248849a-bf6a-4cd3-b297-f9cb6890cf6c
-- title:
--   Theorem 3, p. 4 — with α = 1.5 and f(p) = 1 − (1 − p)^0.663 the sampling algorithm has approximation guarantee less than 3.1 on instances with a depot
-- statement:
--   Consider the sampling algorithm for a priori TSP instances with a depot: sample a set $S$ by including every customer $v$ independently with probability $f(p(v))$, build a master tour on $S$ with a $1.5$-approximation algorithm for TSP, and connect every customer outside $S$ to a nearest customer of $S$ by two parallel edges. Its expected approximation ratio on an instance is at most (2).
--
--   **Theorem.** Let $\alpha = 1.5$ and $f(p) = 1 - (1-p)^\sigma$ with $\sigma = 0.663$. There is a constant $\rho < 3.1$ such that for every finite semi-metric space $(V, c)$, every choice of activation probabilities $0 < p(v) \le 1$ and every depot $d$ with $p(d) = 1$,
--   $$\mathbb E_{S\sim f\circ p}\Big[1.5\cdot\mathrm{OPT}_{\mathrm{TSP}}(S,c) + 2\sum_{v\in V}p(v)\,c(v,S)\Big] \le \rho\cdot\mathrm{OPT}(V, c, p).$$
--
--   The Shmoys–Talwar algorithm samples with $f(p) = p$; with the Christofides–Serdyukov algorithm for the master tour it is a $3.5$-approximation (p. 2). The theorem shows that sampling less improves the guarantee. By Theorem 1 of the paper, the bound transfers to general instances up to an arbitrarily small loss.
--
--   **Formalization Note** The constant is quantified before the instance. The paper's certificate gives $\rho = 3.094$.
--
--   Differences from the source:
--
--   - reading: approximation guarantee less than 3.1 → one ρ < 3.1 with (2) ≤ ρ on every instance with depot; reason: the guarantee of an algorithm is the supremum of its ratio over all instances; this is the stronger of the two readings (the other, (2) < 3.1 on each instance, is weaker)
--   - encoding: the approximation guarantee of the sampling algorithm (with a 1.5-approximation algorithm for TSP) → the bound (2) with α = 1.5 multiplying OPT_TSP(S, c); reason: the paper proves exactly a bound on (2) (p. 4: 'this algorithm has expected approximation ratio at most (2)'; p. 13); the TSP subroutine is not formalized
--   - encoding: an upper bound ρ on the ratio (2) = (1/OPT)·E_{S∼f∘p}[…], with 0/0 := 1 (p. 4) → E_{S∼f∘p}[…] ≤ ρ · OPT; reason: the same statement when OPT > 0; when OPT = 0 the semi-metric vanishes on V, both sides are 0, and the paper's ratio is 1 ≤ ρ; avoids Lean's x/0 = 0
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 4, Theorem 3 (proof p. 13)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting

namespace APrioriTSP.Sampling

/-- Theorem 3 (p. 4): with `α = 1.5` and `f(p) = 1 − (1 − p)^σ`, `σ = 0.663`, there is one
`ρ < 3.1` bounding (2) on every a priori TSP instance with a depot. -/
theorem theorem_3 : ∃ ρ : ℝ, ρ < 3.1 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
      IsDepotInstance c p d →
      samplingCost 1.5 (powerSampling 0.663) c p ≤ ρ * aPrioriOpt c p := by sorry

end APrioriTSP.Sampling
