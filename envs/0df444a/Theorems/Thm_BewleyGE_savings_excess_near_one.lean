-- Prove2me | Theorems.Thm_BewleyGE_savings_excess_near_one
-- name    : BewleyGE.savings_excess_near_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:36:35.27099+00:00
-- url     : https://prove2.me/theorems/b0404fd2-b6f2-4678-8002-e2dbecf54c1c
-- title:
--   Proof of Theorem 1, p.29 (corrected: spread endowments) — savings are in excess supply as $r\to1$
-- statement:
--   If $(p_q,r_q)\in P$ and $r_q\to1$, then there is $N$ such that
--   $$
--   \zeta_{n+1}(p_q,r_q)<0\qquad\text{for all }q>N .
--   $$
--
--   Here $\zeta$ is the excess demand computed from any family $(x^*,V,g,\mu)$ that solves the agents' problem at every $(p,r)\in P$ (Definition 1(i)–(ii)), for an economy satisfying Assumption 1 whose endowment support is spread.
--
--   As $r\to1$ on $\Lambda$ all goods prices tend to $0$ and the savings cap $\sum_ip_i\bar b/(1-r)^2$ tends to infinity; this step handles the corner $(0,\dots,0,1)$ of $\Lambda$, where no good has a positive price and Lemma 8 does not apply.
--
--   Differences from the source:
--   - correction: the §2 endowment model: 𝒴 = 𝒴₁ × ⋯ × 𝒴ₙ with a strict top element y′, which for n ≥ 2 forces 𝒴 to be a single point → a finite set 𝒴 of strictly positive vectors with e > 0, satisfying Spread (y″ ≪ y′ for some y′, y″ ∈ 𝒴); reason: for a singleton 𝒴 = {y₀}, r = 1/β − 1 and any p ≫ 0 on P, every point mass at a ∈ A(p, r) is invariant, so Lemma 2's uniqueness fails and ζ is undefined; the proof of Lemma 8 (pp.26–27) uses exactly the gap that Spread provides
--   - reading: Assumption 1: U continuously differentiable with ∂U(0)/∂xⱼ = ∞; u_p continuously differentiable → U continuous on ℝⁿ₊ and C¹ on the open orthant, (U(t eⱼ) − U(0))/t → ∞ as t ↓ 0; u_p C¹ on (0, ∞); reason: C¹ on the closed orthant contradicts ∂U(0)/∂xⱼ = ∞ and excludes the paper's CES example; u_p′(0+) = ∞ excludes C¹ at 0
--   - reading: U strictly increasing: x > x′ implies U(x) > U(x′), with x > x′ undefined → x′ ≤ x coordinatewise and x′ ≠ x imply U(x′) < U(x); reason: the paper defines only x ≥ x′; the proof of Lemma 8 (p.27) uses this reading
--   - encoding: V(a) = sup over strategies of expected discounted utility (p.6) → V bounded on A(p, r) with TV = V and the maximum attained; reason: the paper's own characterization of V as the unique bounded fixed point of T (p.7, footnote 10)
--   - encoding: μ ∈ P(A(p, r)); integrals over A(p, r) → probability measures on ℝ with μ(A(p, r)ᶜ) = 0; set integrals over A(p, r); reason: the same objects
--   - encoding: ∑_{yᵢ ∈ 𝒴ᵢ} eᵢ(yᵢ) yᵢ → ∑_{y ∈ 𝒴} e(y) yᵢ; reason: the identity the paper uses on p.24; the Lean support has no product structure
--   - encoding: ζ built from the unique g(·, p, r), x*(·, p), μ(·; p, r) of Lemmas 1–2 → ζ built from any family (x, V, g, μ) that satisfies Definition 1(i)–(ii) at every point of P; reason: by Lemmas 1–2 every such family agrees with the paper's objects on A(p, r), so ζ is the paper's; no choice function enters
--   - encoding: g(·, p, r) defined on A(p, r), with no regularity stated in (1) → the savings policy is a measurable function on ℝ (values off A(p, r) otherwise free); reason: the paper's g is continuous on the compact A(p, r) (Lemma 1), so it has measurable extensions, and the wealth operator only sees g on A(p, r); measurability keeps the image measures of (2) from being zero
--   - encoding: (p, r) ∈ ℝⁿ × ℝ, with p_{n+1} := r on p.29 → π : Fin (n + 1) → ℝ, goods i.castSucc, rate Fin.last n; reason: the paper's own convention
--   - reading: r_q > 1/β − 1 for all q > N … imply that ζₙ₊₁(p^q) < 0 for all q > N → along every sequence in P with r_q → 1 there is N with ζₙ₊₁(p_q, r_q) < 0 for q > N; reason: the cited argument needs the savings cap to be large, which holds in the limit r → 1 but not merely for r > 1/β − 1; the proof of Theorem 1 uses only the limit
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Proof of Theorem 1, p.29, "ζn+1(pq) < 0 for all q > N"

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_Spread
import Definitions.Def_BewleyGE_IsEqFamily
import Definitions.Def_BewleyGE_excessDemand

open MeasureTheory Filter Topology

namespace BewleyGE

/-- **Excess supply of savings as the interest rate tends to one.** Light, arXiv:1906.06810v2,
Proof of Theorem 1, p.29: "First assume that pₙ₊₁ = 1 (i.e., r = 1). Then p^q_{n+1} = r_q > 1/β − 1
for all q > N and some N > 0. Combining the results in Chamberlain and Wilson (2000) and Açıkgöz
(2018) … imply that ζₙ₊₁(p^q) < 0 for all q > N."

For every sequence in `P` whose interest rate tends to `1`, the excess demand for savings is
eventually negative.

**Formalization Note.** Read as a statement about the limit (reading R7): along every sequence in
`P` with `r_q → 1` there is `N` with `ζₙ₊₁ < 0` for `q > N`; the page's wording for every `q` with
`r_q > 1/β − 1` has no support in the paper. `ζ` is `excessDemand` for any family solving the
agents' problem on `P`. Endowments are `Spread` (reading R1). -/
theorem savings_excess_near_one {n : ℕ} (E : Economy n) (hA : Assumption1 E) (hS : Spread E)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (V g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (hF : IsEqFamily E x V g μ)
    (πs : ℕ → Fin (n + 1) → ℝ) (hπs : ∀ q, πs q ∈ interiorPrices n)
    (hr : Tendsto (fun q => πs q (Fin.last n)) atTop (𝓝 1)) :
    ∃ N : ℕ, ∀ q, N < q → excessDemand E x g μ (πs q) (Fin.last n) < 0 := by sorry

end BewleyGE
