-- Prove2me | Theorems.Thm_CBCLowerBound_EveryNorm_proposition_9
-- name    : CBCLowerBound.EveryNorm.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:22:37.929444+00:00
-- url     : https://prove2.me/theorems/f016ac57-8f4c-44a3-aa6e-259feda93863
-- title:
--   Proposition 9 — in $\ell_p^D$, $D=2r+1$: $\mathbb E[\mathrm{Alg}]\ge c_0r^2\Lambda/(8D^{1-1/p})$ while $\mathrm{Opt}\le D^{1/p}\Lambda$
-- statement:
--   Let movement costs be $\ell_p$, $p\in[1,\infty]$. There are admissible parameter sequences and a universal constant $c_0>0$ such that, for every tie rule and every $r\ge1$, with $D=2r+1$ and $\Lambda=d_G(s_r,t_r)$ the source-to-target distance of the graph $G=G_r$ used to construct the instance, the following hold. Draw $S_1,\dots,S_T\sim D_r$ and let
--   $$K_t=\mathrm{conv}\{\Psi(v):v\in S_t\}\subseteq\mathbb R^D\qquad\text{(eq. (16))},$$
--   with initial point $x_0=\Psi(s_r)=0$.
--
--   1. Every convex body chasing algorithm $\mathrm{Alg}$ in $(\mathbb R^D,\|\cdot\|_p)$ run on this random sequence of bodies satisfies
--   $$\mathbb E[\mathrm{Alg}]\ \ge\ \frac{c_0\,r^2\,\Lambda}{8\,D^{1-1/p}},$$
--   the expectation being over the request sequence (and the algorithm's randomness).
--   2. Every realized sequence of bodies satisfies $\mathrm{Opt}\le D^{1/p}\Lambda$.
--
--   Together the two clauses lose a factor $8D$, independent of $p$, against the discrete $r^2$ gap of Lemma 3; this gives the $\Omega(d)$ lower bound for every $\ell_p$ norm, and the case $p=2$ feeds the proof of Theorem 1.
--
--   **Formalization Note** $\ell_p^D$ is `PiLp p (fun _ : Fin D => ℝ)`; $1/p$ is $(p^{-1})$ as a real number, which is $0$ for $p=\infty$, so $D^{1-1/p}=D$ and $D^{1/p}=1$ there. Algorithms, expected cost and $\mathrm{Opt}$ are those of the chasing model of the goal theorem, with start point $0$. The expectation over $D_r$ is $\sum_\sigma D_r(\sigma)\,\mathbb E_\omega[\mathrm{Alg}_\omega(K(\sigma))]$ in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: clause 1 for "any convex body chasing algorithm", which the proof takes deterministic after derandomization [BGK+15] → every randomized online algorithm, expectation also over its seed; reason: deterministic algorithms are the one-point-seed case, so the Lean statement specializes to the source's
--   - encoding: "for a suitable choice of the parameter sequences" (the construction of §2) and a universal c₀ → ∃ θ : Params, ∃ c₀ > 0 chosen before the tie rule, r and p; reason: one fixed construction and one constant, as stated
--   - encoding: 1/p for p ∈ [1, ∞] → (p⁻¹).toReal with p : ℝ≥0∞, [Fact (1 ≤ p)]; reason: equals 1/p for finite p and 0 for p = ∞
--   - encoding: x₀ = Ψ(s_r) = 0 → start point 0; reason: Ψ(s_r) = 0 (p.9)
--   - encoding: a realized level-r request sequence → a list of annotated requests in the support of the PMF D_r, read through its plain sets; reason: the annotation records the call structure and does not change the requested sets
--   - reading: "a fixed rule to break a tie" (Stage 3) → the statement holds for both fixed rules (tie : Bool); reason: the paper does not specify the rule
--   - reading: "the final request of this stage consists of the two current vertices" (Stage 2) → the last request of the last Stage-2 call, no extra request; reason: that last request is exactly the pair of current vertices
-- source:
--   Nicolas Christianson, A Linear Lower Bound for Convex Body Chasing in Every Norm, STOC 2027 submission #674 (October 2026), p.14, Proposition 9 (with §4, eq. (16)), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/674.pdf

import Mathlib
import Definitions.Def_CBCLowerBound_EveryNorm_Requests

open scoped ENNReal

namespace CBCLowerBound.EveryNorm

/-- **Proposition 9** (Christianson, STOC 2027 #674, p.14). For a suitable choice `θ` of the
parameter sequences there is a universal constant `c₀ > 0` such that, for every tie rule,
every `r ≥ 1` and every `p ∈ [1, ∞]`, with `D = 2r + 1` and `Λ = L_r = d_G(s_r, t_r)`:
1. every (possibly randomized) convex body chasing algorithm in `ℓ_p^D` started at
   `x₀ = Ψ(s_r) = 0` and run on the bodies `K_t = conv Ψ(S_t)` (eq. (16)) of `σ ∼ D_r` has
   expected movement `E[Alg] ≥ c₀ r² Λ / (8 D^{1−1/p})`;
2. every realized sequence of bodies satisfies `Opt ≤ D^{1/p} Λ`.
Here `1/p` is `0` for `p = ∞`. -/
theorem proposition_9 : ∃ θ : Params, ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (tie : Bool) (r : ℕ), 1 ≤ r →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
      (∀ A : RandomizedAlgorithm (PiLp p fun _ : Fin (2 * r + 1) => ℝ) 0,
        ENNReal.ofReal (c₀ * (r : ℝ) ^ 2 * L θ r /
            (8 * ((2 * r + 1 : ℕ) : ℝ) ^ (1 - (p⁻¹).toReal))) ≤
          ∑' σ, reqDist θ tie r σ * A.expCost (bodies θ r p σ)) ∧
      ∀ σ ∈ (reqDist θ tie r).support,
        opt 0 (bodies θ r p σ) ≤ ((2 * r + 1 : ℕ) : ℝ) ^ (p⁻¹).toReal * L θ r := by sorry

end CBCLowerBound.EveryNorm
