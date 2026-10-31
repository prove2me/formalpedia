-- Prove2me | Theorems.Thm_BewleyGE_lemma_6
-- name    : BewleyGE.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:36:23.28579+00:00
-- url     : https://prove2.me/theorems/db3c7574-9e43-4f65-8553-3c07ae1b6e14
-- title:
--   Lemma 6 — Walras' law
-- statement:
--   For every $(p,r)\in P$,
--   $$
--   (p,r)\cdot\zeta(p,r)=\sum_{i=1}^np_i\,\zeta_i(p,r)+r\,\zeta_{n+1}(p,r)=0 .
--   $$
--
--   Here $\zeta$ is the excess demand computed from any family $(x^*,V,g,\mu)$ that solves the agents' problem at every $(p,r)\in P$ (Definition 1(i)–(ii)), for an economy satisfying Assumption 1 (any finite endowment support).
--
--   Walras' law turns a price at which all excess demands are equal into a price at which they all vanish.
--
--   Differences from the source:
--   - generalization: the §2 endowment model: 𝒴 = 𝒴₁ × ⋯ × 𝒴ₙ with a strict top element y′ (for n ≥ 2 a single point), and ζ computed from the unique μ → any finite set 𝒴 of strictly positive vectors with e > 0 summing to 1 (no product form, no top element, no Spread), and ζ computed from any family satisfying Definition 1(i)–(ii) on P; reason: the identity uses only the budget plane p · x*(c) = c and the invariance μ = Mμ, not the endowment structure or uniqueness of μ; on the paper's economies it gives the printed lemma
--   - reading: Assumption 1: U continuously differentiable with ∂U(0)/∂xⱼ = ∞; u_p continuously differentiable → U continuous on ℝⁿ₊ and C¹ on the open orthant, (U(t eⱼ) − U(0))/t → ∞ as t ↓ 0; u_p C¹ on (0, ∞); reason: C¹ on the closed orthant contradicts ∂U(0)/∂xⱼ = ∞ and excludes the paper's CES example; u_p′(0+) = ∞ excludes C¹ at 0
--   - reading: U strictly increasing: x > x′ implies U(x) > U(x′), with x > x′ undefined → x′ ≤ x coordinatewise and x′ ≠ x imply U(x′) < U(x); reason: the paper defines only x ≥ x′; the proof of Lemma 8 (p.27) uses this reading
--   - encoding: V(a) = sup over strategies of expected discounted utility (p.6) → V bounded on A(p, r) with TV = V and the maximum attained; reason: the paper's own characterization of V as the unique bounded fixed point of T (p.7, footnote 10)
--   - encoding: μ ∈ P(A(p, r)); integrals over A(p, r) → probability measures on ℝ with μ(A(p, r)ᶜ) = 0; set integrals over A(p, r); reason: the same objects
--   - encoding: ∑_{yᵢ ∈ 𝒴ᵢ} eᵢ(yᵢ) yᵢ → ∑_{y ∈ 𝒴} e(y) yᵢ; reason: the identity the paper uses on p.24; the Lean support has no product structure
--   - encoding: ζ built from the unique g(·, p, r), x*(·, p), μ(·; p, r) of Lemmas 1–2 → ζ built from any family (x, V, g, μ) that satisfies Definition 1(i)–(ii) at every point of P; reason: by Lemmas 1–2 every such family agrees with the paper's objects on A(p, r), so ζ is the paper's; no choice function enters
--   - encoding: g(·, p, r) defined on A(p, r), with no regularity stated in (1) → the savings policy is a measurable function on ℝ (values off A(p, r) otherwise free); reason: the paper's g is continuous on the compact A(p, r) (Lemma 1), so it has measurable extensions, and the wealth operator only sees g on A(p, r); measurability keeps the image measures of (2) from being zero
--   - encoding: (p, r) ∈ ℝⁿ × ℝ, with p_{n+1} := r on p.29 → π : Fin (n + 1) → ℝ, goods i.castSucc, rate Fin.last n; reason: the paper's own convention
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Lemma 6, p.24

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_IsEqFamily
import Definitions.Def_BewleyGE_excessDemand

open MeasureTheory

namespace BewleyGE

/-- **Lemma 6 (Walras' law).** Light, arXiv:1906.06810v2, Lemma 6, p.24: "The excess demand
function ζ(p, r) satisfies Walras' law, i.e., (p, r) · ζ(p, r) = 0 for all (p, r) ∈ P."

**Formalization Note.** `(p, r)` is `π : Fin (n + 1) → ℝ` and `(p, r) · ζ = ∑ₖ πₖ ζₖ(π)`; `ζ` is
`excessDemand` for any family solving the agents' problem on `P` (`IsEqFamily`). No endowment
hypothesis beyond the model: the identity uses only the budget plane and invariance, so it holds
for every such family, unique or not. -/
theorem lemma_6 {n : ℕ} (E : Economy n) (hA : Assumption1 E)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (V g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (hF : IsEqFamily E x V g μ) :
    ∀ π ∈ interiorPrices n, ∑ k, π k * excessDemand E x g μ π k = 0 := by sorry

end BewleyGE
