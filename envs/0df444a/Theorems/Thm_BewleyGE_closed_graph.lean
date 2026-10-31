-- Prove2me | Theorems.Thm_BewleyGE_closed_graph
-- name    : BewleyGE.closed_graph
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:36:46.194987+00:00
-- url     : https://prove2.me/theorems/1d5e542f-c11d-4b02-89e5-0da9e23a5e14
-- title:
--   Proof of Theorem 1, pp.29–30 (corrected: spread endowments) — $\Phi$ has nonempty convex compact values and a closed graph
-- statement:
--   For every $p\in\Lambda$, $\Phi(p)$ is a nonempty, convex and compact subset of $\Lambda$, and the graph
--   $$
--   \{(p,p')\in\Lambda\times\Lambda : p'\in\Phi(p)\}
--   $$
--   is closed.
--
--   Here $\Phi(p)=\{z\in\Lambda: z_k=0\ \forall k\notin W(p)\}$, with $W(p)$ the set of markets of maximal excess demand for $p\in P$ and the set of zero coordinates for $p\in\Lambda\setminus P$. Here $\zeta$ is the excess demand computed from any family $(x^*,V,g,\mu)$ that solves the agents' problem at every $(p,r)\in P$ (Definition 1(i)–(ii)), for an economy satisfying Assumption 1 whose endowment support is spread.
--
--   These are the hypotheses of Kakutani's fixed-point theorem for $\Phi$ on the simplex $\Lambda$.
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
--   - encoding: the graph is closed in Λ × Λ (footnote 20) → the graph is closed in ℝⁿ⁺¹ × ℝⁿ⁺¹; reason: Λ is closed and Φ(p) ⊆ Λ, so the two are equivalent
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Proof of Theorem 1, pp.29–30, "We claim that Φ has a closed graph" and footnote 20

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_Spread
import Definitions.Def_BewleyGE_IsEqFamily
import Definitions.Def_BewleyGE_Phi

open MeasureTheory

namespace BewleyGE

/-- **`Φ` has nonempty convex compact values and a closed graph.** Light, arXiv:1906.06810v2,
Proof of Theorem 1, pp.29–30: "It is immediate to establish that Φ(p) is a non-empty, convex and
compact subset of Λ. We claim that Φ has a closed graph. Assume that p^q → p in Λ, π^q → π in Λ,
and π^q ∈ Φ(p^q) for each q. We have to show that π ∈ Φ(p)." Footnote 20: the graph
`{(p, p′) ∈ Λ × Λ : p′ ∈ Φ(p)}` is closed in `Λ × Λ`.

**Formalization Note.** Prices are `π : Fin (n + 1) → ℝ` with the product (Euclidean) topology.
Since `Λ` is closed and `Φ(p) ⊆ Λ`, closedness of the graph in `Λ × Λ` is closedness in the ambient
product. `Φ` is built from `excessDemand` for any family solving the agents' problem on `P`.
Endowments are `Spread` (reading R1). -/
theorem closed_graph {n : ℕ} (E : Economy n) (hA : Assumption1 E) (hS : Spread E)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (V g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (hF : IsEqFamily E x V g μ) :
    (∀ π ∈ priceSimplex n,
      (Phi E x g μ π).Nonempty ∧ Convex ℝ (Phi E x g μ π) ∧ IsCompact (Phi E x g μ π) ∧
        Phi E x g μ π ⊆ priceSimplex n) ∧
    IsClosed {z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) |
      z.1 ∈ priceSimplex n ∧ z.2 ∈ Phi E x g μ z.1} := by sorry

end BewleyGE
