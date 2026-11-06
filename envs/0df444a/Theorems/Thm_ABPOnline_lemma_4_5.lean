-- Prove2me | Theorems.Thm_ABPOnline_lemma_4_5
-- name    : ABPOnline.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:56:36.515437+00:00
-- url     : https://prove2.me/theorems/127fd4a0-ac91-4929-808b-24be916bcba9
-- title:
--   Lemma 4.5 — final-block confinement of the Euler scheme
-- statement:
--   Fix an even integer $p>4$ and $c_F>0$. There are $h_0=h_0(p,c_F)>0$, a radius $s_p(\cdot,c_F)$ continuous on $(0,h_0)$ with $s_p(h,c_F)\downarrow0$ as $h\downarrow0$, and feedbacks $v_N$ with the following property. Let $L_N\in\{1,\dots,N-1\}$, $h_N=L_N/N$, and suppose $h_N$ lies in a fixed compact subinterval of $(0,h_0)$. For independent Brownian coordinates the Euler scheme
--   $$
--   \hat Z_{0,i}=0,\quad \hat a_{k,i}=v_N(k/N,\hat Z_{k,i}),\quad \hat Z_{k+1,i}=\hat Z_{k,i}+\frac{\hat a_{k,i}}{N}+B_i\big(\tfrac{k+1}N\big)-B_i\big(\tfrac kN\big)
--   $$
--   satisfies
--   $$
--   \sup_{k<L_N}\|\hat a_{k,i}\|_{L^p}\le c_F,\qquad \mathbb E\max_{i\le M}\operatorname{dist}\big(\hat Z_{L_N,i},[-s_p(h_N,c_F),s_p(h_N,c_F)]\big)=O(M^{1/p}N^{-1}),
--   $$
--   where the implied constant depends only on $p$, $c_F$ and the compact range of $h_N$. In particular, if $M=O(N)$ the right-hand side is $o(1)$.
--
--   The final block of Algorithm 1 uses this feedback to confine all $M$ coordinates simultaneously.
--
--   Differences from the source:
--   - encoding: h₀, s_p, an explicit feedback v_N, and the estimates (19)–(21) with an implied constant → ∃ (h₀, s_p, v) with IsFinalBlockFeedback p c_F h₀ s_p v: v a measurable family indexed by (N, L_N), chosen before the compact range and the constant C; reason: the paper's v_N = v_{h_N} is one construction (97), fixed before the range; "explicit" has no formal content
--   - encoding: dist(Ẑ, [−s, s]); E max_{i≤M}; O(M^{1/p}N^{−1}) → max(|Ẑ| − s, 0); a lower integral of a supremum in ℝ≥0∞; ≤ C·M^{1/p}/N; reason: equal for s ≥ 0, and s_p ≥ 0 follows from monotonicity and the limit 0; no junk value
--   - encoding: "for independent Brownian coordinates" → for every M and every M-dimensional Brownian motion on [0, 1] (IsBrownianVec) on every probability space in Type; reason: the estimates are statements about laws
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Lemma 4.5, (19)–(21), p.13 (PDF p.14); proof in §C.4, pp.40–43

import Mathlib
import Definitions.Def_ABPOnline_IsFinalBlockFeedback

set_option autoImplicit false

namespace ABPOnline

/-- **Lemma 4.5 (Final-block confinement)** (arXiv:2609.02124, printed p.13, PDF p.14). Fix an
even integer `p > 4` and `c_F > 0`. There are `h₀ = h₀(p, c_F) > 0` and a radius `s_p(·, c_F)`,
continuous on `(0, h₀)` and satisfying `s_p(h, c_F) ↓ 0` as `h ↓ 0`, with the following property.
Let `L_N ∈ {1, …, N−1}`, put `h_N = L_N/N`, and suppose that `h_N` lies in a fixed compact
subinterval of `(0, h₀)`. There is a feedback `v_N` on `[0, h_N)` such that, for independent
Brownian coordinates, the Euler scheme (19) satisfies the per-step drift bound (20)
`sup_{k<L_N} ‖â_{k,i}‖_{L^p} ≤ c_F` and the terminal confinement estimate (21)
`E max_{i≤M} dist(Ẑ_{L_N,i}, [−s_p(h_N, c_F), s_p(h_N, c_F)]) = O(M^{1/p} N^{−1})`.

**Formalization Note** The property is `IsFinalBlockFeedback` (see its docstring): the constant of
`O(·)` depends only on `p`, `c_F` and the compact range of `h_N`; the feedback is a measurable
family `v N L_N`. The word "explicit" is not formalized. The closing remark ("if `M = O(N)` the
right-hand side is `o(1)`") is a conjunct of `IsFinalBlockFeedback`. -/
theorem lemma_4_5 (p : ℕ) (hp : Even p) (hp4 : 4 < p) (cF : ℝ) (hcF : 0 < cF) :
    ∃ (h₀ : ℝ) (sp : ℝ → ℝ) (v : ℕ → ℕ → ℝ → ℝ → ℝ), IsFinalBlockFeedback p cF h₀ sp v := by sorry

end ABPOnline
