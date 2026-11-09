-- Prove2me | Theorems.Thm_CBCLowerBound_EveryNorm_lemma_3
-- name    : CBCLowerBound.EveryNorm.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:00.308227+00:00
-- url     : https://prove2.me/theorems/68274ec6-9a75-45c7-8ac6-918b7b8f4cf9
-- title:
--   Lemma 3 (Bubeck–Coester–Rabani) — every randomized online algorithm pays $\mathbb E[\mathrm{Alg}]\ge c_0r^2L_r$ on $D_r$
-- statement:
--   There are admissible parameter sequences $(m_r,C_r)_{r\ge0}$ (one fixed choice for all levels) and a universal constant $c_0>0$ such that the following holds for every tie rule and every level $r\ge1$. Let $G_r$ be the level-$r$ graph with source $s_r$ and $L_r=d_{G_r}(s_r,t_r)$, the offline optimal cost of every sequence of $D_r$ (Lemma 2). Every (possibly randomized) online algorithm $\mathrm{Alg}$ for the discrete requests starting at $s_r$ satisfies
--   $$\mathbb E[\mathrm{Alg}(\sigma)]\ \ge\ c_0\,r^2\,L_r,$$
--   where the expectation is over $\sigma\sim D_r$ and the algorithm's randomness.
--
--   This is the discrete lower bound of Bubeck, Coester and Rabani (STOC 2023, §§3.3–3.6) for their small-request construction; Proposition 9 transfers it to convex body chasing.
--
--   **Formalization Note** A randomized algorithm is in the distributional form of p.4: a probability vector on the vertices after each prefix, supported in the newest request, starting at $\delta_{s_r}$, paying $\sum_t W_1(P_{t-1},P_t)$. The expectation over the algorithm's randomness is this transportation cost; the expectation over $\sigma$ is $\sum_\sigma D_r(\sigma)\,\mathrm{cost}(\sigma)$ in $[0,\infty]$. The $\Omega(r^2)$ of the lemma is stated in the explicit form the paper gives on p.8.
--
--   Differences from the source:
--   - encoding: E[Alg(σ)] ≥ Ω(r²)·L_r → the explicit form of p.8, ∃ c₀ > 0 with E[Alg(σ)] ≥ c₀ r² L_r for all r ≥ 1; reason: the paper restates the lemma in this form
--   - encoding: "for a suitable choice of the parameter sequences m_r and C_r" → ∃ θ : Params before c₀ and r; reason: one fixed choice of sequences, as on p.7
--   - encoding: a (possibly randomized) online algorithm on the discrete requests → a sequence of probability vectors chosen online, paying the W₁ distance between consecutive ones; reason: this is the paper's model of randomized MSS algorithms (p.4)
--   - encoding: a realized level-r request sequence → a list of annotated requests in the support of the PMF D_r, read through its plain sets; reason: the annotation records the call structure and does not change the requested sets
--   - reading: "a fixed rule to break a tie" (Stage 3) → the statement holds for both fixed rules (tie : Bool); reason: the paper does not specify the rule
--   - reading: "the final request of this stage consists of the two current vertices" (Stage 2) → the last request of the last Stage-2 call, no extra request; reason: that last request is exactly the pair of current vertices
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.7, Lemma 3 (citing Bubeck, Coester and Rabani, STOC 2023, Sections 3.3–3.6), explicit form p.8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib
import Definitions.Def_CBCLowerBound_EveryNorm_Requests

open scoped ENNReal

namespace CBCLowerBound.EveryNorm

/-- **Lemma 3** (Bubeck–Coester–Rabani, §§3.3–3.6; Christianson, STOC 2027 #674, p.7, in the
explicit form stated on p.8). For a suitable choice `θ` of the parameter sequences there is a
universal constant `c₀ > 0` such that, for every tie rule, every level `r ≥ 1` and every
(possibly randomized) online algorithm on the discrete requests starting at `s_r`,
`E[Alg(σ)] ≥ c₀ r² L_r`, the expectation being over `σ ∼ D_r` and the algorithm's
randomness. -/
theorem lemma_3 : ∃ θ : Params, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (tie : Bool) (r : ℕ), 1 ≤ r →
    ∀ A : MSSAlg θ r,
      ENNReal.ofReal (c₀ * (r : ℝ) ^ 2 * L θ r) ≤
        ∑' σ, reqDist θ tie r σ * ENNReal.ofReal (A.cost (requests σ)) := by sorry

end CBCLowerBound.EveryNorm
