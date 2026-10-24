-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_lemma_15
-- name    : APrioriTSP.Sampling.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:52.837834+00:00
-- url     : https://prove2.me/theorems/0a8209c6-4bd6-4e40-8e46-55b27ab3fb17
-- title:
--   Lemma 15, p. 12 — the reciprocal of the optimum value of (Sampling-LP) bounds (2) for f(p) = 1 − (1 − p)^σ on all instances with depot
-- statement:
--   Let $N \ge 1$ be an integer, $\beta > 0$, $\alpha \ge 0$ and $\sigma \in (0,1)$, and let $\mu > 0$ be a lower bound on the optimum value of (Sampling-LP), i.e. $\mu \le \sum_{i=0}^N e^{-(i+1/2)\beta}B_i$ for every feasible $(B, M)$ of (13)–(17). Then for every instance $(V, c, p)$ of the a priori TSP with a depot,
--   $$\mathbb E_{S\sim f\circ p}\Big[\alpha\cdot\mathrm{OPT}_{\mathrm{TSP}}(S,c) + 2\sum_{v\in V}p(v)\,c(v,S)\Big] \le \frac1\mu\cdot\mathrm{OPT},\qquad f(x) = 1 - (1-x)^\sigma .$$
--   Taking $\mu$ equal to the optimum value gives the paper's form: its reciprocal is an upper bound on the approximation guarantee of the sampling algorithm.
--
--   This is the single finite linear program of §2 whose value controls the sampling algorithm on all instances with a depot, for every instance size and every activation probability.
--
--   Differences from the source:
--
--   - encoding: N an integer → N ∈ ℕ with 1 ≤ N; reason: the LP has the variables B_0, …, B_N and constraint (13) (resp. (19)) uses B_1 (resp. the index k = 1), so the printed LP is defined only for N ≥ 1
--   - encoding: the reciprocal of the optimum value v* of (Sampling-LP) → μ⁻¹ for every μ > 0 with μ ≤ Σ_{i=0}^N e^{−(i+1/2)β}·B_i for every feasible (B, M); reason: v* is the supremum of such μ, so the family of bounds is the bound 1/v*; if v* = 0 the paper's bound is +∞ and no such μ exists
--   - encoding: the approximation guarantee of the sampling algorithm (using an α-approximation algorithm for TSP) → the bound (2): E_{S∼f∘p}[α·OPT_TSP(S, c) + 2·Σ_v p(v)·c(v, S)] compared with OPT; reason: the paper bounds exactly (2) (p. 4: 'this algorithm has expected approximation ratio at most (2)'; p. 13: 'an upper bound on (2)'); the TSP subroutine itself is not formalized
--   - encoding: an upper bound ρ on the ratio (2) = (1/OPT)·E_{S∼f∘p}[…], with 0/0 := 1 (p. 4) → E_{S∼f∘p}[…] ≤ ρ · OPT; reason: the same statement when OPT > 0; when OPT = 0 the semi-metric vanishes on V, both sides are 0, and the paper's ratio is 1 ≤ ρ; avoids Lean's x/0 = 0
--   - generalization: α ≥ 1, the approximation guarantee of the TSP algorithm of step (ii) (p. 4) → every real α ≥ 0; reason: (2) is a formula in α and the argument uses only α ≥ 0; at every α ≥ 1 the Lean statement is the paper's
--   - generalization: σ = 0.663, fixed at the start of §2 (p. 7) → every σ ∈ (0, 1); reason: the argument uses only 0 < σ < 1, the range of Lemma 9 (ii); σ = 0.663 is an instance
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 12, Lemma 15 and (Sampling-LP) (13)–(17) (proof p. 13)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- Lemma 15 (p. 12): if `μ > 0` is a lower bound on the optimum value of (Sampling-LP), then
`1/μ` bounds (2) for `f(p) = 1 − (1 − p)^σ` on every instance with a depot. -/
theorem lemma_15 (α σ β μ : ℝ) (N : ℕ) (hN : 1 ≤ N) (hβ : 0 < β) (hα : 0 ≤ α)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (hμ : 0 < μ)
    (hval : ∀ (B : ℕ → ℝ) (M : ℕ → ℕ → ℝ), SamplingLPFeasible α σ β N B M →
      μ ≤ samplingLPObj β N B) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (p : V → ℝ) (d : V),
      IsDepotInstance c p d →
      samplingCost α (powerSampling σ) c p ≤ μ⁻¹ * aPrioriOpt c p := by sorry

end APrioriTSP.Sampling
