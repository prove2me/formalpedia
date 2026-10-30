-- Prove2me | Theorems.Thm_APrioriTSP_Sampling_bucket_feasible_samplingLP
-- name    : APrioriTSP.Sampling.bucket_feasible_samplingLP
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T14:15:32.031363+00:00
-- url     : https://prove2.me/theorems/6aecbfe4-f651-4adb-868a-644590a77e97
-- title:
--   Proof of Lemma 15, p. 13 — buckets of a feasible (Sampling-OP) solution give a feasible (Sampling-LP) solution
-- statement:
--   Let $\alpha\ge 0$, $0<\sigma<1$, $\beta>0$, let $N\in\mathbb N$, and let $b$ be an odd integer with $b>\beta$; put $p=\beta/b\in(0,1)$. Let $C=(C_i)_{i\ge 1}$ be a feasible solution of (Sampling-OP) for $p$, i.e.
--
--   1. $C_i\ge 0$ for $i\ge 1$ (6);
--   2. $C_{i+j}\le C_i+C_j$ for $i,j\ge 1$ (7);
--   3. $\sum_{k\ge 1}(1-\sigma p)^{k-1}\big(\alpha C_k+2p\sum_{i=1}^{k-1}\min\{C_i,C_{k-i}\}\big)\ge\sigma^{-2}$ (8).
--
--   Let $B_i=\sum_{j=\max\{1,\,ib-(b-1)/2\}}^{ib+(b-1)/2}C_j$ ($i\ge 0$) be the buckets (9) and $M_{i,j}=\min\{B_i,B_j\}$. Then $(B_0,\dots,B_N,M)$ is a feasible solution of (Sampling-LP):
--   $$(\alpha+\delta_1)\sum_{k=0}^N e^{-(k-1)\sigma\beta}B_k+\delta_2B_1+4\beta\sum_{j=0}^N\sum_{i=0}^j e^{-(i+j-1)\sigma\beta}M_{i,j}\ \ge\ \sigma^{-2},$$
--   $B_{i+j}\le B_i+B_j$ for $1\le i\le j$, $i+j\le N$, $M_{i,j}\le B_i$, $M_{i,j}\le B_j$ for $0\le i\le j\le N$, and $B,M\ge 0$. Here $\delta_1,\delta_2$ are the constants of Lemma 14.
--
--   This is the first step of the proof of Lemma 15 ("for any feasible solution $C$ to (Sampling-OP) we obtain a feasible solution $(B,M)$ to (Sampling-LP) via (9) and $M_{i,j}=\min\{B_i,B_j\}$"). It packages the chain (8) $\to$ Lemma 13 $\to$ (10) $\to$ Lemma 14 $\to$ (11) of pp. 10–12, together with Proposition 12 for constraint (14).
--
--   **Formalization Note** Feasibility for (Sampling-OP) and (Sampling-LP) are the platform predicates `SamplingOPFeasible α σ (β / b) C` and `SamplingLPFeasible α σ β N B M`; the buckets are `bucket b C`.
-- source:
--   Blauth, Neuwohner, Puhlmann & Vygen, Improved guarantees for the a priori TSP, arXiv:2309.10663v1, p. 13, proof of Lemma 15, first sentence (summarizing pp. 9–12: (8), (9), Lemma 13, (10), Lemma 14, (11), Proposition 12, constraints (13)–(17))

import Mathlib
import Definitions.Def_APrioriTSP_Sampling_Setting
import Definitions.Def_APrioriTSP_Sampling_LP

namespace APrioriTSP.Sampling

/-- p. 13 (proof of Lemma 15), summarizing pp. 9–12: for `p = β / b` with `b` odd, the buckets
`B = bucket b C` of (9) of a feasible solution `C` of (Sampling-OP), together with
`M_{i,j} = min {B_i, B_j}`, form a feasible solution of (Sampling-LP). -/
theorem bucket_feasible_samplingLP (α σ β : ℝ) (N : ℕ) (hβ : 0 < β) (hα : 0 ≤ α)
    (hσ0 : 0 < σ) (hσ1 : σ < 1) (b : ℕ) (hb : Odd b) (hbβ : β < b) (C : ℕ → ℝ)
    (hC : SamplingOPFeasible α σ (β / b) C) :
    SamplingLPFeasible α σ β N (bucket b C) (fun i j => min (bucket b C i) (bucket b C j)) := by
  sorry

end APrioriTSP.Sampling
