-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_lemma_11
-- name    : APrioriTSP.Sampling.lemma_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:39:33.454493+00:00
-- url     : https://prove2.me/theorems/77a8be3b-02d5-463f-ae4d-640aec7d47d1
-- title:
--   Lemma 11, p. 9 — the reciprocal of the value of (Sampling-OP) bounds (2) for f(p) = σp on all p-normalized instances
-- statement:
--   Fix $\alpha \ge 0$, $\sigma \in (0,1)$ and $0 < p < 1$, and let $v^*$ be the value (infimum) of (Sampling-OP): minimize $\sum_{i\ge1}(1-p)^{i-1}C_i$ over sequences with $C_i \ge 0$ (6), $C_i + C_j \ge C_{i+j}$ (7) and the sampling constraint (8). Let $\mu > 0$ be any lower bound on $v^*$, i.e. $\mu \le \sum_{i\ge1}(1-p)^{i-1}C_i$ for every feasible $C$. Then for every $p$-normalized instance $(V, c, p_V)$ with depot $d$, sampling every customer other than the depot with probability $\sigma p$ (and the depot with probability $1$) gives
--   $$\mathbb E_{S\sim f\circ p_V}\Big[\alpha\cdot\mathrm{OPT}_{\mathrm{TSP}}(S,c) + 2\sum_{v\in V} p_V(v)\, c(v,S)\Big] \le \frac1\mu\cdot\mathrm{OPT},\qquad f(x) = \sigma x\ (x<1),\ f(1) = 1 .$$
--   Taking $\mu = v^*$ when $v^* > 0$ gives the paper's form: $1/v^*$ bounds (2) on all $p$-normalized instances.
--
--   This is the first reduction of §2: the hop sums of an optimum tour form a feasible point of (Sampling-OP), up to scaling, and the problem no longer depends on the instance size.
--
--   **Formalization Note** The constraint (8) and the objective are `tsum`s with the index shift $k \mapsto k+1$; for $C$ satisfying (6)–(7) both series converge.
--
--   Differences from the source:
--
--   - encoding: the reciprocal of the value v* of (Sampling-OP) → μ⁻¹ for every μ > 0 with μ ≤ Σ_{i≥1}(1 − p)^{i−1}C_i for every feasible C; reason: v* is the supremum of such μ, so the family of bounds is the bound 1/v*; if v* = 0 the paper's bound is +∞ and no such μ exists
--   - encoding: the approximation guarantee of the sampling algorithm (using an α-approximation algorithm for TSP) → the bound (2): E_{S∼f∘p}[α·OPT_TSP(S, c) + 2·Σ_v p(v)·c(v, S)] compared with OPT; reason: the paper bounds exactly (2) (p. 4: 'this algorithm has expected approximation ratio at most (2)'; p. 13: 'an upper bound on (2)'); the TSP subroutine itself is not formalized
--   - encoding: an upper bound ρ on the ratio (2) = (1/OPT)·E_{S∼f∘p}[…], with 0/0 := 1 (p. 4) → E_{S∼f∘p}[…] ≤ ρ · OPT; reason: the same statement when OPT > 0; when OPT = 0 the semi-metric vanishes on V, both sides are 0, and the paper's ratio is 1 ≤ ρ; avoids Lean's x/0 = 0
--   - generalization: α ≥ 1, the approximation guarantee of the TSP algorithm of step (ii) (p. 4) → every real α ≥ 0; reason: (2) is a formula in α and the argument uses only α ≥ 0; at every α ≥ 1 the Lean statement is the paper's
--   - generalization: σ = 0.663, fixed at the start of §2 (p. 7) → every σ ∈ (0, 1); reason: the argument uses only 0 < σ < 1, the range of Lemma 9 (ii); σ = 0.663 is an instance
--   - encoding: Σ_{k=1}^∞ (1 − σp)^{k−1} · (α·C_k + 2p·Σ_{i=1}^{k−1} min{C_i, C_{k−i}}) in (8) → Σ_{k≥0} (1 − σp)^k · (α·C_{k+1} + 2p·Σ_{i=1}^{k} min{C_i, C_{k+1−i}}) (index k ↦ k + 1), a `tsum`; reason: the same series; it converges for every C satisfying (6)–(7) since C_k ≤ k·C_1 and 0 < σp < 1
--   - encoding: f(p) = σp → f(x) = σx for x ≠ 1 and f(1) = 1 (`linSampling`); reason: the algorithm requires f(1) = 1 (p. 4), so the depot is always sampled; on a p-normalized instance with p < 1 every other customer has p(v) = p ≠ 1 and is sampled with probability σp
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 9, Lemma 11 and (Sampling-OP) (6)–(8)

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- Lemma 11 (p. 9): for `0 < p < 1`, if `μ > 0` is a lower bound on the value of
(Sampling-OP), then `1/μ` bounds (2) for `f(p) = σ p` on every `p`-normalized instance. -/
theorem lemma_11 (α σ p μ : ℝ) (hα : 0 ≤ α) (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (hp0 : 0 < p) (hp1 : p < 1) (hμ : 0 < μ)
    (hval : ∀ C : ℕ → ℝ, SamplingOPFeasible α σ p C → μ ≤ samplingOPObj p C) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (c : V → V → ℝ) (pf : V → ℝ) (d : V),
      IsNormalized c pf d p →
      samplingCost α (linSampling σ) c pf ≤ μ⁻¹ * aPrioriOpt c pf := by sorry

end APrioriTSP.Sampling
