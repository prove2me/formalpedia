-- Prove2me | Theorems.Thm_ABPOnline_Supplement_theorem_5_3
-- name    : ABPOnline.Supplement.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:36:52.087099+00:00
-- url     : https://prove2.me/theorems/43d68cdd-0c36-4a23-99a5-c8585de29bdb
-- title:
--   Theorem 5.3 — $V_\kappa(\eta)=-2a_0\log H_0(0)$ for piecewise-constant weights
-- statement:
--   Let $B$ be a standard Brownian motion on $[0,1]$ and $\kappa\in\mathbb R$. Let
--   $$
--   0=t_0<t_1<\dots<t_m=1,\qquad \eta(t)=a_i>0\quad(t_i\le t<t_{i+1}),
--   $$
--   and write $\Delta_i=t_{i+1}-t_i$. Define
--   $$
--   H_{m-1}:=P_{\Delta_{m-1}}\mathbf 1_{[\kappa,\infty)}
--   $$
--   and, for $i=m-2,\dots,0$,
--   $$
--   H_i:=P_{\Delta_i}\big(H_{i+1}^{a_{i+1}/a_i}\big),
--   $$
--   where $P_s$ is the one-dimensional heat semigroup. Then the weighted $L^2$ relaxation of the Brownian control value satisfies
--   $$
--   V_\kappa(\eta)=-2a_0\log H_0(0).
--   $$
--
--   For normalized weights $V_\kappa(\eta)\le E_\star(\kappa)$, so this identity turns lower bounds on $E_\star$ into a one-dimensional computation; it is the basis of the lower bound in Theorem 1.2.
--
--   **Formalization Note** $V_\kappa(\eta)$ is an extended nonnegative real; the right-hand side, which is nonnegative, is embedded as an extended real. The grid and the weights are $\mathbb N$-indexed sequences with $m\ge1$.
--
--   Differences from the source:
--   - generalization: B a standard Brownian motion (B_t)_{0≤t≤1} with its completed natural filtration → the statement holds for every process B with IsBrownianOn1 B P on every probability space, with V_κ(η) computed on that B; reason: V_κ(η) depends only on the law of B; the source's Brownian motion is one such process
--   - generalization: η normalized, ∫₀¹ η(t) dt = Σ a_i Δ_i = 1 (standing assumption of §5.1) → no normalization of the a_i; reason: both sides are positively homogeneous of degree one in (a_0, …, a_{m−1}) (each H_i depends only on ratios), so the normalized case is a special case
--   - encoding: V_κ(η) a value in [0, ∞) → V_κ(η) in ℝ≥0∞, right-hand side embedded by ENNReal.ofReal; reason: the right-hand side is nonnegative since 0 < H_0(0) ≤ 1; same identity
-- source:
--   Jo, Lee, The Exact Online Threshold for the Asymmetric Binary Perceptron, arXiv:2609.02124 (artifact sha256 bd5e2bdb18a47b7e806191ae9b888a6e4e7e150a9bd50e541b7587007d07a7a2), Theorem 5.3, (38)–(40), p.20 (PDF p.21)

import Mathlib
import Definitions.Def_ABPOnline_IsBrownianOn1
import Definitions.Def_ABPOnline_Supplement_Vrelax
import Definitions.Def_ABPOnline_Supplement_dpH

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ABPOnline.Supplement

/-- **Theorem 5.3** (Jo–Lee, arXiv:2609.02124, printed p.20, PDF p.21). Let
`0 = t₀ < t₁ < ⋯ < t_m = 1` and `η(t) = a_i > 0` for `t_i ≤ t < t_{i+1}`, `Δ_i = t_{i+1} − t_i`.
With `H_{m-1} := P_{Δ_{m-1}} 1_{[κ,∞)}` (38) and `H_i := P_{Δ_i}(H_{i+1}^{a_{i+1}/a_i})` for
`i = m-2, …, 0` (39), the weighted relaxation value is `V_κ(η) = −2a₀ log H₀(0)` (40).

**Formalization Note** `V_κ(η)` is `Vrelax` (in `ℝ≥0∞`), computed on an arbitrary standard
Brownian motion `B` on `[0,1]` on an arbitrary probability space; the right-hand side is embedded
by `ENNReal.ofReal` (it is nonnegative since `0 < H₀(0) ≤ 1`). The grid and the weights are
`ℕ`-indexed sequences of which `t 0, …, t m` and `a 0, …, a (m-1)` are used; `m ≥ 1`. The weight
`η` is `pcWeight m t a`. The normalization `∫₀¹ η = ∑ a_i Δ_i = 1` of §5.1 is not assumed: both
sides are positively homogeneous of degree one in `η`, so the identity for normalized weights is
the special case. The identity holds for every `κ ∈ ℝ`. -/
theorem theorem_5_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianOn1 B P) (κ : ℝ) (m : ℕ) (hm : 1 ≤ m) (t a : ℕ → ℝ)
    (ht0 : t 0 = 0) (htm : t m = 1) (ht : ∀ i < m, t i < t (i + 1)) (ha : ∀ i < m, 0 < a i) :
    Vrelax P B κ (pcWeight m t a) =
      ENNReal.ofReal (-2 * a 0 * Real.log (dpH κ m t a 0 0)) := by sorry

end ABPOnline.Supplement
