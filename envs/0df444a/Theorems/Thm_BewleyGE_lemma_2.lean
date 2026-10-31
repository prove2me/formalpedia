-- Prove2me | Theorems.Thm_BewleyGE_lemma_2
-- name    : BewleyGE.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:33:02.639269+00:00
-- url     : https://prove2.me/theorems/ce1b1c38-526c-4bf0-be01-212d0cfcd1a6
-- title:
--   Lemma 2 (corrected: spread endowments) — a unique invariant wealth distribution, globally attracting
-- statement:
--   Let the economy satisfy Assumption 1 and have a spread endowment support. Fix $(p,r)\in P$, i.e. $p\gg0$, $r>0$, $\sum_ip_i+r=1$, and let $x^*$, $V$, $g$ be the demand function, value function and savings policy at $(p,r)$. Then there is exactly one invariant wealth distribution $\mu\in\mathcal P(A(p,r))$, $\mu=M\mu$, and for every $\lambda\in\mathcal P(A(p,r))$ the iterates converge weakly:
--   $$
--   M^k\lambda\ \Rightarrow\ \mu\qquad(k\to\infty).
--   $$
--
--   The lemma makes the stationary wealth distribution, and hence the excess demand, a well-defined function of prices.
--
--   Differences from the source:
--   - correction: the §2 endowment model: 𝒴 = 𝒴₁ × ⋯ × 𝒴ₙ with a strict top element y′, which for n ≥ 2 forces 𝒴 to be a single point → a finite set 𝒴 of strictly positive vectors with e > 0, satisfying Spread (y″ ≪ y′ for some y′, y″ ∈ 𝒴); reason: for a singleton 𝒴 = {y₀}, r = 1/β − 1 and any p ≫ 0 on P, every point mass at a ∈ A(p, r) is invariant, so Lemma 2's uniqueness fails and ζ is undefined; the proof of Lemma 8 (pp.26–27) uses exactly the gap that Spread provides
--   - reading: Assumption 1: U continuously differentiable with ∂U(0)/∂xⱼ = ∞; u_p continuously differentiable → U continuous on ℝⁿ₊ and C¹ on the open orthant, (U(t eⱼ) − U(0))/t → ∞ as t ↓ 0; u_p C¹ on (0, ∞); reason: C¹ on the closed orthant contradicts ∂U(0)/∂xⱼ = ∞ and excludes the paper's CES example; u_p′(0+) = ∞ excludes C¹ at 0
--   - reading: U strictly increasing: x > x′ implies U(x) > U(x′), with x > x′ undefined → x′ ≤ x coordinatewise and x′ ≠ x imply U(x′) < U(x); reason: the paper defines only x ≥ x′; the proof of Lemma 8 (p.27) uses this reading
--   - encoding: V(a) = sup over strategies of expected discounted utility (p.6) → V bounded on A(p, r) with TV = V and the maximum attained; reason: the paper's own characterization of V as the unique bounded fixed point of T (p.7, footnote 10)
--   - encoding: μ ∈ P(A(p, r)); integrals over A(p, r) → probability measures on ℝ with μ(A(p, r)ᶜ) = 0; set integrals over A(p, r); reason: the same objects
--   - encoding: g(·, p, r) defined on A(p, r), with no regularity stated in (1) → the savings policy is a measurable function on ℝ (values off A(p, r) otherwise free); reason: the paper's g is continuous on the compact A(p, r) (Lemma 1), so it has measurable extensions, and the wealth operator only sees g on A(p, r); measurability keeps the image measures of (2) from being zero
--   - encoding: weak convergence of {Mⁿλ} → ∫ f d(Mᵏλ) → ∫ f dμ for every bounded continuous f : ℝ → ℝ; reason: the definition of weak convergence
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Lemma 2, p.21

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_Spread
import Definitions.Def_BewleyGE_IsDemand
import Definitions.Def_BewleyGE_IsValueFunction
import Definitions.Def_BewleyGE_IsSavingsPolicy
import Definitions.Def_BewleyGE_IsInvariantDist
import Definitions.Def_BewleyGE_WeakConv

open MeasureTheory

namespace BewleyGE

/-- **Lemma 2 (unique invariant wealth distribution).** Light, arXiv:1906.06810v2, Lemma 2,
p.21: "For every (p, r) ∈ P there exists a unique invariant wealth distribution
μ(·; p, r) ∈ P(A(p, r)). Furthermore, for all λ(·; p, r) ∈ P(A(p, r)), the sequence of measures
{Mⁿλ} converges weakly to μ(·; p, r) ∈ P(A(p, r))."

**Formalization Note.** `(p, r) ∈ P` is `p ≫ 0`, `r > 0`, `∑ pᵢ + r = 1`. The demand `x`, value
function `V` and policy `g` at `(p, r)` are hypotheses (they exist and are unique on `A(p, r)` by
Lemma 1). `P(A(p, r))` is the set of probability measures on `ℝ` null off `A(p, r)`. The endowment
support is assumed `Spread` (reading R1): for a singleton support the lemma is false. -/
theorem lemma_2 {n : ℕ} (E : Economy n) (hA : Assumption1 E) (hS : Spread E)
    (p : Fin n → ℝ) (r : ℝ) (hp : ∀ i, 0 < p i) (hr : 0 < r) (hsum : ∑ i, p i + r = 1)
    (x : ℝ → Fin n → ℝ) (V g : ℝ → ℝ) (hx : IsDemand E p x)
    (hV : IsValueFunction E p r x V) (hg : IsSavingsPolicy E p r x V g) :
    ∃ μ : Measure ℝ, IsInvariantDist E p r g μ ∧
      (∀ μ' : Measure ℝ, IsInvariantDist E p r g μ' → μ' = μ) ∧
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ν (wealthSet E p r)ᶜ = 0 →
        WeakConv (fun k => (wealthOperator E p r g)^[k] ν) μ := by sorry

end BewleyGE
