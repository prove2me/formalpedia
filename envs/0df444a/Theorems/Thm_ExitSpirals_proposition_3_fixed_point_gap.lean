-- Prove2me | Theorems.Thm_ExitSpirals_proposition_3_fixed_point_gap
-- name    : ExitSpirals.proposition_3_fixed_point_gap
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:03:07.038507+00:00
-- url     : https://prove2.me/theorems/8e85f3ae-1e24-482d-bb1f-2222b99c15d7
-- title:
--   Proof of Proposition 3, A.5 (corrected: no tangency assumed, $s^*\le1$, C7) — the limit activity vanishes below $x_{crit}$ and has a positive gap above
-- statement:
--   Let $p_R,p_C$ be joint degree distributions with $p_{0k,R}=p_{0k,C}=0$ for all $k$ (Assumption 4.5) and $\sum_{j,k}jk\,p_{jk}<\infty$. Let $a(x)=s^*(x)\,g_C(s^*(x))$ be the limit activity, with $s^*(x)$ the greatest fixed point of $F(s,x)=x\,g_R(x\,g_C(s))$. Then there are $x_{crit}\in(0,1]$ and $A>0$ such that
--   $$a(x)=0\quad\text{for }0\le x<x_{crit},\qquad a(x)\ge A\quad\text{for }x_{crit}<x\le1.$$
--
--   This is the deterministic half of Proposition 3: the fixed point does not decay continuously to zero but drops from at least $A$ to $0$ at $x_{crit}$. The case $x_{crit}=1$ (any shock leads to complete collapse) is included.
--
--   Differences from the source:
--   - correction: p.56: 'a region above x_c where a non trivial solution 0 < s* < 1 exists' → a(x) ≥ A > 0 for x_crit < x ≤ 1 (no upper bound s* < 1); reason: at x = 1 under Assumption 4.5 the greatest solution is s* = 1 (F(1, 1) = 1, and by Lemma 2 every agent is active)
--   - correction: s* of the printed (9) and 'Â = s*' → a(x) = s* g_C(s*) with the corrected in-degree g_µ; reason: C1 and C3: the printed g uses out-degrees and the printed activity counts support through R only; both vanish exactly when the corrected ones do, so the dichotomy is the page's
--   - generalization: a tangency point x_c with ∂F/∂s(s*, x_c) = 1, assumed to exist; the no-tangency case treated separately ('a minimal disturbance of the network leads always to a complete collapse') → no tangency assumed; one statement covering both cases, with x_crit ∈ (0, 1]; reason: both cases of the page are instances; x_crit = 1 is the collapse case
--   - generalization: Assumption 4.6 (giant component concavity), used through Lemma 10(4) → not assumed; reason: the dichotomy needs only monotonicity of F and the vanishing of g_µ below 1/ρ_µ; adding the assumption gives the source's statement
--   - generalization: 'a non trivial solution … exists' for each x > x_c → a single A > 0 with a(x) ≥ A for every x > x_crit; reason: a uniform gap is what makes the transition discontinuous and implies the pointwise statement
--   - reading: finite Σ_jk j k p_jk (needed for the critical s_c,µ of Proposition 4 that the proof uses) → hypothesis Summable (j k p_jk) for both laws; reason: the section's standing Assumption A.1(3) (Σ_i (d⁺_i)² + (d⁻_i)² = O(n)) passes to the limit law by Fatou and implies it; the page's proof invokes 'λ < ∞' for the existence of s_c,µ, which needs this moment
-- source:
--   Aymanns, Georg, Golub, Exit Spirals in Coupled Networked Markets, SSRN 2881814 (preprint, sha256 12000f11…6c84d2), Appendix A.5, proof of Proposition 3, pp.55–56 (summary, p.56)

import Mathlib
import Definitions.Def_ExitSpirals_IsDegreeDist
import Definitions.Def_ExitSpirals_coupledMap

namespace ExitSpirals

/-- **Proof of Proposition 3, Appendix A.5: the limit activity `a(x)` vanishes below a critical
`x_crit` and is bounded below by a fixed positive constant above it.**
Aymanns, Georg, Golub, *Exit Spirals in Coupled Networked Markets*, SSRN 2881814, Appendix A.5,
proof of Proposition 3, p.56: "In summary, if there exists some fixed point of F(x, s), s*, and a
shock of a critical size 1 − x_c such that F(x, s) is tangent to the diagonal
(∂F/∂s(s*, x_c) = 1), then there will be a region below x_c where only the trivial solution exists
(s* = 0) and a region above x_c where a non trivial solution 0 < s* < 1 exists."

For joint degree distributions `p_R`, `p_C` with `p_{0k} = 0` (Assumption 4.5) and finite
`Σ_{jk} j k p_{jk}`, there are `x_crit ∈ (0, 1]` and `A > 0` such that `a(x) = 0` for
`0 ≤ x < x_crit` and `a(x) ≥ A` for `x_crit < x ≤ 1`, where `a = limitActivity`.

**Formalization Note.** No tangency is assumed: the page's tangent case and its "no tangency"
case (p.56, "a minimal disturbance of the network leads always to a complete collapse") are both
covered, so `x_crit = 1` is allowed. Assumption 4.6 (giant component concavity) is not assumed.
The page's strict `s* < 1` is not claimed: at `x = 1` the greatest solution is `1`. -/
theorem proposition_3_fixed_point_gap (pR pC : ℕ → ℕ → ℝ) (hpR : IsDegreeDist pR)
    (hpC : IsDegreeDist pC) (h45R : ∀ k, pR 0 k = 0) (h45C : ∀ k, pC 0 k = 0)
    (h2R : Summable fun jk : ℕ × ℕ => (jk.1 : ℝ) * jk.2 * pR jk.1 jk.2)
    (h2C : Summable fun jk : ℕ × ℕ => (jk.1 : ℝ) * jk.2 * pC jk.1 jk.2) :
    ∃ xcrit ∈ Set.Ioc (0 : ℝ) 1, ∃ A : ℝ, 0 < A ∧
      (∀ x ∈ Set.Ico (0 : ℝ) xcrit, limitActivity pR pC x = 0) ∧
      (∀ x ∈ Set.Ioc xcrit 1, A ≤ limitActivity pR pC x) := by sorry

end ExitSpirals
