-- Prove2me | Theorems.Thm_BewleyGE_lemma_7
-- name    : BewleyGE.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:46.947005+00:00
-- url     : https://prove2.me/theorems/2bbc22b3-c38c-46ed-9e7d-479483ac6208
-- title:
--   Lemma 7 — lower bounds on the excess demand
-- statement:
--   For every $\delta\in(0,1)$ there is $\xi>0$ such that
--   $$
--   \zeta_i(p,r)\ge-\xi\quad(1\le i\le n,\ (p,r)\in P),\qquad \zeta_{n+1}(p,r)\ge-\xi\quad((p,r)\in P,\ r\le\delta).
--   $$
--
--   Here $\zeta$ is the excess demand computed from any family $(x^*,V,g,\mu)$ that solves the agents' problem at every $(p,r)\in P$ (Definition 1(i)–(ii)), for an economy satisfying Assumption 1 (any finite endowment support).
--
--   The bounds are part of the boundary behaviour needed for the closed-graph argument.
--
--   Differences from the source:
--   - generalization: the §2 endowment model: 𝒴 = 𝒴₁ × ⋯ × 𝒴ₙ with a strict top element y′ (for n ≥ 2 a single point), and ζ computed from the unique μ → any finite set 𝒴 of strictly positive vectors with e > 0 summing to 1 (no product form, no top element, no Spread), and ζ computed from any family satisfying Definition 1(i)–(ii) on P; reason: the bounds use only x* ≥ 0 and g ≤ ∑ pᵢ b̄/(1 − r)², not the endowment structure or uniqueness of μ; on the paper's economies it gives the printed lemma
--   - reading: Assumption 1: U continuously differentiable with ∂U(0)/∂xⱼ = ∞; u_p continuously differentiable → U continuous on ℝⁿ₊ and C¹ on the open orthant, (U(t eⱼ) − U(0))/t → ∞ as t ↓ 0; u_p C¹ on (0, ∞); reason: C¹ on the closed orthant contradicts ∂U(0)/∂xⱼ = ∞ and excludes the paper's CES example; u_p′(0+) = ∞ excludes C¹ at 0
--   - reading: U strictly increasing: x > x′ implies U(x) > U(x′), with x > x′ undefined → x′ ≤ x coordinatewise and x′ ≠ x imply U(x′) < U(x); reason: the paper defines only x ≥ x′; the proof of Lemma 8 (p.27) uses this reading
--   - encoding: V(a) = sup over strategies of expected discounted utility (p.6) → V bounded on A(p, r) with TV = V and the maximum attained; reason: the paper's own characterization of V as the unique bounded fixed point of T (p.7, footnote 10)
--   - encoding: μ ∈ P(A(p, r)); integrals over A(p, r) → probability measures on ℝ with μ(A(p, r)ᶜ) = 0; set integrals over A(p, r); reason: the same objects
--   - encoding: ∑_{yᵢ ∈ 𝒴ᵢ} eᵢ(yᵢ) yᵢ → ∑_{y ∈ 𝒴} e(y) yᵢ; reason: the identity the paper uses on p.24; the Lean support has no product structure
--   - encoding: ζ built from the unique g(·, p, r), x*(·, p), μ(·; p, r) of Lemmas 1–2 → ζ built from any family (x, V, g, μ) that satisfies Definition 1(i)–(ii) at every point of P; reason: by Lemmas 1–2 every such family agrees with the paper's objects on A(p, r), so ζ is the paper's; no choice function enters
--   - encoding: g(·, p, r) defined on A(p, r), with no regularity stated in (1) → the savings policy is a measurable function on ℝ (values off A(p, r) otherwise free); reason: the paper's g is continuous on the compact A(p, r) (Lemma 1), so it has measurable extensions, and the wealth operator only sees g on A(p, r); measurability keeps the image measures of (2) from being zero
--   - encoding: (p, r) ∈ ℝⁿ × ℝ, with p_{n+1} := r on p.29 → π : Fin (n + 1) → ℝ, goods i.castSucc, rate Fin.last n; reason: the paper's own convention
--   - reading: ξ > 0 with ζₙ₊₁ ≥ −ξ for all (p, r) ∈ P with r ≤ δ < 1 "for some δ ∈ (0, 1)" → for every δ ∈ (0, 1) there is ξ > 0 bounding all goods coordinates and, for r ≤ δ, the savings coordinate; reason: the proof's ξ is b̄/(1 − δ)²; a ξ uniform in δ is false since savings reach b̄/(1 − r)² → ∞; the proof of Theorem 1 (p.29) uses it this way
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Lemma 7, p.25

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_IsEqFamily
import Definitions.Def_BewleyGE_excessDemand

open MeasureTheory

namespace BewleyGE

/-- **Lemma 7 (lower bounds on the excess demand).** Light, arXiv:1906.06810v2, Lemma 7, p.25:
"There exists ξ > 0 such that ζᵢ(p, r) ≥ −ξ for all 1 ≤ i ≤ n and all (p, r) ∈ P, and
ζₙ₊₁(p, r) ≥ −ξ for all (p, r) ∈ P such that r ≤ δ < 1 for some δ ∈ (0, 1)."

**Formalization Note.** The quantifiers are read as: for every `δ ∈ (0, 1)` there is `ξ > 0` with
both bounds (reading R6); the proof's `ξ` is `b̄/(1 − δ)²`, and a `ξ` uniform in `δ` is false for
savings. The goods bound is uniform in any case. `ζ` is `excessDemand` for any family solving
the agents' problem on `P`. No endowment hypothesis beyond the model: the bounds use only
`x* ≥ 0` and `g ≤ ∑ pᵢ b̄/(1 − r)²`, so they hold for every such family. -/
theorem lemma_7 {n : ℕ} (E : Economy n) (hA : Assumption1 E)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (V g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (hF : IsEqFamily E x V g μ) :
    ∀ δ : ℝ, 0 < δ → δ < 1 → ∃ ξ : ℝ, 0 < ξ ∧
      (∀ π ∈ interiorPrices n, ∀ i : Fin n, -ξ ≤ excessDemand E x g μ π i.castSucc) ∧
      (∀ π ∈ interiorPrices n, π (Fin.last n) ≤ δ →
        -ξ ≤ excessDemand E x g μ π (Fin.last n)) := by sorry

end BewleyGE
