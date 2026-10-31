-- Prove2me | Theorems.Thm_BewleyGE_proposition_2
-- name    : BewleyGE.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:35:44.70901+00:00
-- url     : https://prove2.me/theorems/11e6cff1-4ee1-4dc3-8c5c-5b9921726d2d
-- title:
--   Proposition 2 (corrected: spread endowments) — continuity, Walras' law, boundary and bounds of $\zeta$
-- statement:
--   The excess demand function $\zeta:P\to\mathbb R^{n+1}$ satisfies:
--
--   1. $\zeta$ is continuous on $P$;
--   2. Walras' law: $(p,r)\cdot\zeta(p,r)=0$ for all $(p,r)\in P$;
--   3. if $(p_q,r_q)\in P$ converges to $(p,r)\in\Lambda\setminus P$ with $p_k>0$ for some good $k\le n$, then $\|\zeta(p_q,r_q)\|_1\to\infty$;
--   4. if $(p_q,r_q)\in P$ converges to $(p,r)$ and $p_k>0$, then $\{\zeta_k(p_q,r_q)\}$ is bounded; if $r\in(0,1)$, then $\{\zeta_{n+1}(p_q,r_q)\}$ is bounded;
--   5. for every $\delta\in(0,1)$ there is $\xi>0$ with $\zeta_i\ge-\xi$ on $P$ for every good $i$ and $\zeta_{n+1}\ge-\xi$ on $P\cap\{r\le\delta\}$.
--
--   Here $\zeta$ is the excess demand computed from any family $(x^*,V,g,\mu)$ that solves the agents' problem at every $(p,r)\in P$ (Definition 1(i)–(ii)), for an economy satisfying Assumption 1 whose endowment support is spread.
--
--   These are the properties from which the proof of Theorem 1 extracts a zero of $\\zeta$.
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
--   - encoding: ‖ζ‖₁ = ∑ⱼ |ζⱼ| and "the sequence is bounded" → ∑ over all n + 1 coordinates of |ζₖ|; ∃ C, ∀ q, |ζₖ(p_q, r_q)| ≤ C; reason: the paper's definitions (p.20)
--   - reading: ξ > 0 with ζₙ₊₁ ≥ −ξ for all (p, r) ∈ P with r ≤ δ < 1 "for some δ ∈ (0, 1)" → for every δ ∈ (0, 1) there is ξ > 0 bounding all goods coordinates and, for r ≤ δ, the savings coordinate; reason: the proof's ξ is b̄/(1 − δ)²; a ξ uniform in δ is false since savings reach b̄/(1 − r)² → ∞; the proof of Theorem 1 (p.29) uses it this way
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Proposition 2, p.20

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_Spread
import Definitions.Def_BewleyGE_IsEqFamily
import Definitions.Def_BewleyGE_excessDemand

open MeasureTheory Filter Topology

namespace BewleyGE

/-- **Proposition 2 (properties of the excess demand).** Light, arXiv:1906.06810v2,
Proposition 2, p.20: "The excess demand function ζ : P → Rⁿ⁺¹ satisfies the following properties.
(i) The function ζ is continuous. (ii) The function ζ satisfies Walras' law, i.e.,
(p, r) · ζ(p, r) = 0 for all (p, r) ∈ P. (iii) If (p_q, r_q) → (p, r) = (p₁, …, pₙ, r) ∈ Λ\P with
{p_q, r_q} ⊆ P and p_k > 0 for some 1 ≤ k ≤ n, then lim_{q→∞} ‖ζ(p_q, r_q)‖₁ = ∞. (iv) If
{p_q, r_q} ⊆ P, (p_q, r_q) → (p, r) = (p₁, …, pₙ, r) and p_k > 0, then the sequence
{ζ_k(p_q, r_q)} of the kth components of {ζ(p_q, r_q)} is bounded. Similarly, r ∈ (0, 1) implies
that the sequence {ζₙ₊₁(p_q, r_q)} is bounded. (v) There exists ξ > 0 such that ζᵢ(p, r) ≥ −ξ for
all 1 ≤ i ≤ n and all (p, r) ∈ P, and ζₙ₊₁(p, r) ≥ −ξ for all (p, r) ∈ P such that r ≤ δ < 1 for
some δ ∈ (0, 1)."

**Formalization Note.** The five clauses are the conjunction of Lemmas 5–8 in the encodings of
those items: `(p, r)` is `π : Fin (n + 1) → ℝ`; `‖·‖₁` sums all `n + 1` coordinates; (v) is read as
"for every `δ ∈ (0, 1)` there is `ξ > 0`" (reading R6). `ζ` is `excessDemand` for any family
solving the agents' problem on `P`. Endowments are `Spread` (reading R1). -/
theorem proposition_2 {n : ℕ} (E : Economy n) (hA : Assumption1 E) (hS : Spread E)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (V g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (hF : IsEqFamily E x V g μ) :
    ContinuousOn (excessDemand E x g μ) (interiorPrices n) ∧
    (∀ π ∈ interiorPrices n, ∑ k, π k * excessDemand E x g μ π k = 0) ∧
    (∀ (πs : ℕ → Fin (n + 1) → ℝ) (π : Fin (n + 1) → ℝ),
      (∀ q, πs q ∈ interiorPrices n) → Tendsto πs atTop (𝓝 π) →
      π ∈ priceSimplex n → π ∉ interiorPrices n → (∃ k : Fin n, 0 < π k.castSucc) →
      Tendsto (fun q => ∑ k, |excessDemand E x g μ (πs q) k|) atTop atTop) ∧
    (∀ (πs : ℕ → Fin (n + 1) → ℝ) (π : Fin (n + 1) → ℝ),
      (∀ q, πs q ∈ interiorPrices n) → Tendsto πs atTop (𝓝 π) →
      (∀ k : Fin n, 0 < π k.castSucc →
        ∃ C : ℝ, ∀ q, |excessDemand E x g μ (πs q) k.castSucc| ≤ C) ∧
      (0 < π (Fin.last n) → π (Fin.last n) < 1 →
        ∃ C : ℝ, ∀ q, |excessDemand E x g μ (πs q) (Fin.last n)| ≤ C)) ∧
    (∀ δ : ℝ, 0 < δ → δ < 1 → ∃ ξ : ℝ, 0 < ξ ∧
      (∀ π ∈ interiorPrices n, ∀ i : Fin n, -ξ ≤ excessDemand E x g μ π i.castSucc) ∧
      (∀ π ∈ interiorPrices n, π (Fin.last n) ≤ δ →
        -ξ ≤ excessDemand E x g μ π (Fin.last n))) := by sorry

end BewleyGE
