-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_corollary_16
-- name    : APrioriTSP.Sampling.corollary_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:40:00.773836+00:00
-- url     : https://prove2.me/theorems/f6838b87-7fb1-4fa0-a871-2d8aed01ee0c
-- title:
--   Corollary 16, p. 13 — any feasible solution (x, y, v, w) of (Dual-Sampling-LP) certifies the bound σ²/y on (2)
-- statement:
--   Let $N \ge 1$ be an integer, $\beta > 0$, $\alpha \ge 0$ and $\sigma \in (0,1)$. Let $(x, y, v, w)$ be a feasible solution of (Dual-Sampling-LP), constraints (18)–(20), with $y > 0$. Then for every instance $(V, c, p)$ of the a priori TSP with a depot,
--   $$\mathbb E_{S\sim f\circ p}\Big[\alpha\cdot\mathrm{OPT}_{\mathrm{TSP}}(S,c) + 2\sum_{v\in V}p(v)\,c(v,S)\Big] \le \frac{\sigma^2}{y}\cdot\mathrm{OPT},\qquad f(x) = 1 - (1-x)^\sigma .$$
--
--   The corollary turns the analysis into a finite certificate: any dual-feasible point with $\sigma^2/y < 3.1$ at $\alpha = 1.5$, $\sigma = 0.663$ proves Theorem 3.
--
--   **Formalization Note** At $y = 0$ the paper's bound $\sigma^2/0$ is $+\infty$ and says nothing, while Lean's $\sigma^2/0 = 0$ would claim (2) $\le 0$; the hypothesis $y > 0$ excludes exactly that case.
--
--   Differences from the source:
--
--   - encoding: N an integer → N ∈ ℕ with 1 ≤ N; reason: the LP has the variables B_0, …, B_N and constraint (13) (resp. (19)) uses B_1 (resp. the index k = 1), so the printed LP is defined only for N ≥ 1
--   - encoding: any feasible (x, y, v, w), with the bound σ²/y → feasible (x, y, v, w) with y > 0; reason: at y = 0 the paper's bound σ²/0 = +∞ is empty, while Lean's σ²/0 = 0 is not the paper's value
--   - encoding: the approximation ratio of the sampling algorithm restricted to instances with depot → the bound (2): E_{S∼f∘p}[α·OPT_TSP(S, c) + 2·Σ_v p(v)·c(v, S)] compared with OPT; reason: the paper bounds exactly (2) (p. 4; p. 13: 'an upper bound on (2)'); the TSP subroutine itself is not formalized
--   - encoding: an upper bound ρ on the ratio (2) = (1/OPT)·E_{S∼f∘p}[…], with 0/0 := 1 (p. 4) → E_{S∼f∘p}[…] ≤ ρ · OPT; reason: the same statement when OPT > 0; when OPT = 0 the semi-metric vanishes on V, both sides are 0, and the paper's ratio is 1 ≤ ρ; avoids Lean's x/0 = 0
--   - generalization: α ≥ 1, the approximation guarantee of the TSP algorithm of step (ii) (p. 4) → every real α ≥ 0; reason: (2) is a formula in α and the argument uses only α ≥ 0; at every α ≥ 1 the Lean statement is the paper's
--   - generalization: σ = 0.663, fixed at the start of §2 (p. 7) → every σ ∈ (0, 1); reason: the argument uses only 0 < σ < 1, the range of Lemma 9 (ii); σ = 0.663 is an instance
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 13, Corollary 16 and (Dual-Sampling-LP) (18)–(20)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- Corollary 16 (p. 13): every feasible solution `(x, y, v, w)` of (Dual-Sampling-LP) with
`y > 0` certifies the bound `σ²/y` on (2) for `f(p) = 1 − (1 − p)^σ` on every instance with a
depot. -/
theorem corollary_16 (α σ β : ℝ) (N : ℕ) (hN : 1 ≤ N) (hβ : 0 < β) (hα : 0 ≤ α)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℕ → ℕ → ℝ) (y : ℝ) (v w : ℕ → ℕ → ℝ)
    (hfeas : DualSamplingLPFeasible α σ β N x y v w) (hy : 0 < y) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
      IsDepotInstance c p d →
      samplingCost α (powerSampling σ) c p ≤ σ ^ 2 / y * aPrioriOpt c p := by sorry

end APrioriTSP.Sampling
