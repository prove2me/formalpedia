-- Prove2me | Theorems.Thm_BewleyGE_theorem_1
-- name    : BewleyGE.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:22.644818+00:00
-- url     : https://prove2.me/theorems/7472a2fa-51a4-47ac-b5e3-ce7bb2726110
-- title:
--   Theorem 1 — a competitive stationary equilibrium exists
-- statement:
--   Consider an economy with $n\ge2$ goods, a finite support $\mathcal Y$ of strictly positive endowment vectors with probabilities $e(y)>0$, a discount factor $\tfrac12<\beta<1$, a savings cap constant $\bar b>0$ and a utility $U$ satisfying Assumption 1, and suppose that $\mathcal Y$ is either a single point or spread. Then there exist prices $p\gg0$ and an interest rate $r\in(0,1)$ with
--   $$
--   \sum_{i=1}^np_i+r=1,
--   $$
--   a demand function $x^*$, a value function $V$, a savings policy $g$ and a wealth distribution $\mu\in\mathcal P(A(p,r))$ forming a **competitive stationary equilibrium**: $x^*$ and $g$ are optimal, $\mu=M\mu$, and
--   $$
--   \int_{A(p,r)}x^*_i\big(a-g(a),p\big)\,\mu(da)=\sum_{y\in\mathcal Y}e(y)\,y_i\quad(i=1,\dots,n),\qquad \int_{A(p,r)}g(a)\,\mu(da)=0 .
--   $$
--
--   This is the existence theorem for a Bewley–Huggett economy with many goods in which both the goods prices and the interest rate are determined in equilibrium.
--
--   **Formalization Note** When $\mathcal Y=\{y_0\}$ the paper's proof does not apply (the invariant distribution is not unique); there an equilibrium is given directly by $r=1/\beta-1$, $p$ proportional to $\nabla U(y_0)$ normalized to $\sum_ip_i+r=1$, savings $0$ at wealth $p\cdot y_0$, and $\mu$ the point mass at $p\cdot y_0$.
--
--   Differences from the source:
--   - generalization: 𝒴 = 𝒴₁ × ⋯ × 𝒴ₙ with e > 0, y ≫ 0 and a strict top element y′ (for n ≥ 2 this forces 𝒴 to be a single point) → any finite set 𝒴 of strictly positive vectors with e > 0 summing to 1 that is a singleton or Spread; reason: covers the literal (singleton) model and every non-degenerate reading: a joint support with a strict top element, a product with non-degenerate marginals
--   - reading: Assumption 1: U continuously differentiable with ∂U(0)/∂xⱼ = ∞; u_p continuously differentiable → U continuous on ℝⁿ₊ and C¹ on the open orthant, (U(t eⱼ) − U(0))/t → ∞ as t ↓ 0; u_p C¹ on (0, ∞); reason: C¹ on the closed orthant contradicts ∂U(0)/∂xⱼ = ∞ and excludes the paper's CES example; u_p′(0+) = ∞ excludes C¹ at 0
--   - reading: U strictly increasing: x > x′ implies U(x) > U(x′), with x > x′ undefined → x′ ≤ x coordinatewise and x′ ≠ x imply U(x′) < U(x); reason: the paper defines only x ≥ x′; the proof of Lemma 8 (p.27) uses this reading
--   - encoding: V(a) = sup over strategies of expected discounted utility (p.6) → V bounded on A(p, r) with TV = V and the maximum attained; reason: the paper's own characterization of V as the unique bounded fixed point of T (p.7, footnote 10)
--   - encoding: μ ∈ P(A(p, r)); integrals over A(p, r) → probability measures on ℝ with μ(A(p, r)ᶜ) = 0; set integrals over A(p, r); reason: the same objects
--   - encoding: ∑_{yᵢ ∈ 𝒴ᵢ} eᵢ(yᵢ) yᵢ → ∑_{y ∈ 𝒴} e(y) yᵢ; reason: the identity the paper uses on p.24; the Lean support has no product structure
--   - encoding: g and x* as in Definition 1 (no regularity stated) → g measurable and the integrands of (iii) and (iv) integrable on A(p, r); reason: the paper's g is continuous on the compact A(p, r) and x* is bounded there (Lemma 1), so its objects satisfy these clauses; they keep the integrals from taking junk values
--   - generalization: "there exists a competitive stationary equilibrium" → there is one whose prices are normalized, ∑ pᵢ + r = 1; reason: forgetting the normalization gives the source statement; the proof constructs (p, r) ∈ P (p.11)
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Theorem 1, p.10 (restated p.20); Definition 1, pp.8–9

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_Spread
import Definitions.Def_BewleyGE_IsCSE

open MeasureTheory

namespace BewleyGE

/-- **Theorem 1 (existence of a competitive stationary equilibrium).**
Light, *General equilibrium in a heterogeneous-agent incomplete-market economy*,
arXiv:1906.06810v2, Theorem 1, p.10 (restated p.20): "Suppose that Assumption 1 holds. Then,
there exists a competitive stationary equilibrium."

For every economy (`n ≥ 2` goods, finite strictly positive endowment support with positive
probabilities, `1/2 < β < 1`, `b̄ > 0`) whose utility satisfies Assumption 1 and whose endowment
support is a singleton or spread, there are prices `p ≫ 0`, `0 < r < 1` with `∑ pᵢ + r = 1`, a
demand function `x`, a value function `V`, a savings policy `g` and a wealth distribution `μ`
forming a CSE (Definition 1: optimality, invariance, clearing of every good market and of the
bond market).

**Formalization Note.** The endowment hypothesis `𝒴.card = 1 ∨ Spread` replaces the page's
product support with a strict top element, which for `n ≥ 2` forces a singleton (reading R1); it
covers the literal reading and every non-degenerate one. The normalization `∑ pᵢ + r = 1` is what
the proof constructs ("prices (p, r) ∈ P", p.11). In the singleton case the paper's proof does
not apply (the invariant law is not unique); there a CSE is given directly by `r = 1/β − 1`,
`p` proportional to `∇U(y₀)`, `g = 0` at wealth `p · y₀` and `μ` the point mass there. -/
theorem theorem_1 {n : ℕ} (E : Economy n) (hA : Assumption1 E)
    (hY : E.Y.card = 1 ∨ Spread E) :
    ∃ (p : Fin n → ℝ) (r : ℝ) (x : ℝ → Fin n → ℝ) (V g : ℝ → ℝ) (μ : Measure ℝ),
      ∑ i, p i + r = 1 ∧ IsCSE E p r x V g μ := by sorry

end BewleyGE
