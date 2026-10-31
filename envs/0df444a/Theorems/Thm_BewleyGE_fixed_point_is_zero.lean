-- Prove2me | Theorems.Thm_BewleyGE_fixed_point_is_zero
-- name    : BewleyGE.fixed_point_is_zero
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:36:24.007212+00:00
-- url     : https://prove2.me/theorems/e8c18e84-a735-4405-8c3d-f267b56c4c9e
-- title:
--   Proof of Theorem 1, p.30 — a fixed point of $\Phi$ is an equilibrium price
-- statement:
--   If $p\in\Lambda$ and $p\in\Phi(p)$, then $p\in P$ and
--   $$
--   \zeta(p)=0 .
--   $$
--
--   Here $\zeta$ is the excess demand computed from any family $(x^*,V,g,\mu)$ that solves the agents' problem at every $(p,r)\in P$ (Definition 1(i)–(ii)), for an economy satisfying Assumption 1 (any finite endowment support).
--
--   With Kakutani's theorem this yields prices $(p,r)\in P$ at which every good market and the bond market clear, which together with the agents' solution at $(p,r)$ is a competitive stationary equilibrium.
--
--   Differences from the source:
--   - generalization: the §2 endowment model: 𝒴 = 𝒴₁ × ⋯ × 𝒴ₙ with a strict top element y′ (for n ≥ 2 a single point), and ζ computed from the unique μ → any finite set 𝒴 of strictly positive vectors with e > 0 summing to 1 (no product form, no top element, no Spread), and ζ computed from any family satisfying Definition 1(i)–(ii) on P; reason: the step uses only Walras' law (Lemma 6), which needs neither the endowment structure nor uniqueness of μ; on the paper's economies it gives the printed step
--   - reading: Assumption 1: U continuously differentiable with ∂U(0)/∂xⱼ = ∞; u_p continuously differentiable → U continuous on ℝⁿ₊ and C¹ on the open orthant, (U(t eⱼ) − U(0))/t → ∞ as t ↓ 0; u_p C¹ on (0, ∞); reason: C¹ on the closed orthant contradicts ∂U(0)/∂xⱼ = ∞ and excludes the paper's CES example; u_p′(0+) = ∞ excludes C¹ at 0
--   - reading: U strictly increasing: x > x′ implies U(x) > U(x′), with x > x′ undefined → x′ ≤ x coordinatewise and x′ ≠ x imply U(x′) < U(x); reason: the paper defines only x ≥ x′; the proof of Lemma 8 (p.27) uses this reading
--   - encoding: V(a) = sup over strategies of expected discounted utility (p.6) → V bounded on A(p, r) with TV = V and the maximum attained; reason: the paper's own characterization of V as the unique bounded fixed point of T (p.7, footnote 10)
--   - encoding: μ ∈ P(A(p, r)); integrals over A(p, r) → probability measures on ℝ with μ(A(p, r)ᶜ) = 0; set integrals over A(p, r); reason: the same objects
--   - encoding: ∑_{yᵢ ∈ 𝒴ᵢ} eᵢ(yᵢ) yᵢ → ∑_{y ∈ 𝒴} e(y) yᵢ; reason: the identity the paper uses on p.24; the Lean support has no product structure
--   - encoding: ζ built from the unique g(·, p, r), x*(·, p), μ(·; p, r) of Lemmas 1–2 → ζ built from any family (x, V, g, μ) that satisfies Definition 1(i)–(ii) at every point of P; reason: by Lemmas 1–2 every such family agrees with the paper's objects on A(p, r), so ζ is the paper's; no choice function enters
--   - encoding: g(·, p, r) defined on A(p, r), with no regularity stated in (1) → the savings policy is a measurable function on ℝ (values off A(p, r) otherwise free); reason: the paper's g is continuous on the compact A(p, r) (Lemma 1), so it has measurable extensions, and the wealth operator only sees g on A(p, r); measurability keeps the image measures of (2) from being zero
--   - encoding: (p, r) ∈ ℝⁿ × ℝ, with p_{n+1} := r on p.29 → π : Fin (n + 1) → ℝ, goods i.castSucc, rate Fin.last n; reason: the paper's own convention
--   - encoding: p is a CSE → p ∈ P and ζ(p) = 0; reason: what the proof establishes; by §3.1 (p.10) such p with the family's g, x*, μ is a CSE
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Proof of Theorem 1, p.30, "We claim that p is a CSE"

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_IsEqFamily
import Definitions.Def_BewleyGE_Phi
import Definitions.Def_BewleyGE_interiorPrices

open MeasureTheory

namespace BewleyGE

/-- **A fixed point of `Φ` is an equilibrium price.** Light, arXiv:1906.06810v2, Proof of
Theorem 1, p.30: "We claim that p is a CSE. First note that p ≫ 0. … Hence, γ = ζᵢ(p) for
i = 1, …, n + 1. From Warlas' law we have γ = ∑ pᵢ m = ∑ pᵢ ζᵢ(p) = 0 which implies ζ(p) = 0
because p ≫ 0. Thus, p is a CSE."

Every `π ∈ Λ` with `π ∈ Φ(π)` lies in `P` and is a zero of the excess demand.

**Formalization Note.** "`p` is a CSE" is stated as its content in the proof: `p ∈ P` and
`ζ(p) = 0` (by Definition 1 and §3.1, p.10, such prices with the family's `g`, `x*`, `μ` form a CSE).
`ζ` and `Φ` are built from any family solving the agents' problem on `P`. No endowment hypothesis
beyond the model: the step uses only Walras' law, which holds for every such family. -/
theorem fixed_point_is_zero {n : ℕ} (E : Economy n) (hA : Assumption1 E)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (V g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (hF : IsEqFamily E x V g μ) :
    ∀ π ∈ priceSimplex n, π ∈ Phi E x g μ π →
      π ∈ interiorPrices n ∧ excessDemand E x g μ π = 0 := by sorry

end BewleyGE
