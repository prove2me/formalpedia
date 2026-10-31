-- Prove2me | Theorems.Thm_BewleyGE_lemma_8
-- name    : BewleyGE.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:36:04.365074+00:00
-- url     : https://prove2.me/theorems/9f0ffcc4-8903-405d-b1f1-e78d6b08f147
-- title:
--   Lemma 8 (corrected: spread endowments) — boundary and boundedness conditions
-- statement:
--   1. If $(p_q,r_q)\in P$ converges to $(p,r)\in\Lambda\setminus P$ and $p_k>0$ for some good $k\le n$, then
--   $$
--   \lim_{q\to\infty}\|\zeta(p_q,r_q)\|_1=\infty,\qquad \|z\|_1=\sum_{j=1}^{n+1}|z_j| .
--   $$
--   2. If $(p_q,r_q)\in P$ converges to $(p,r)$ and $p_k>0$ for a good $k\le n$, then $\{\zeta_k(p_q,r_q)\}_q$ is bounded; if $r\in(0,1)$, then $\{\zeta_{n+1}(p_q,r_q)\}_q$ is bounded.
--
--   Here $\zeta$ is the excess demand computed from any family $(x^*,V,g,\mu)$ that solves the agents' problem at every $(p,r)\in P$ (Definition 1(i)–(ii)), for an economy satisfying Assumption 1 whose endowment support is spread.
--
--   Part 1 replaces the usual Arrow–Debreu boundary condition, which only holds here when some good keeps a positive price.
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
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Lemma 8, p.25

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_Spread
import Definitions.Def_BewleyGE_IsEqFamily
import Definitions.Def_BewleyGE_excessDemand

open MeasureTheory Filter Topology

namespace BewleyGE

/-- **Lemma 8 (boundary and boundedness conditions).** Light, arXiv:1906.06810v2, Lemma 8,
p.25:
"(i) If (p_q, r_q) → (p, r) = (p₁, …, pₙ, r) ∈ Λ\P with {p_q, r_q} ⊆ P and p_k > 0 for some
1 ≤ k ≤ n, then lim_{q→∞} ‖ζ(p_q, r_q)‖₁ = ∞.
(ii) If {p_q, r_q} ⊆ P, (p_q, r_q) → (p, r) = (p₁, …, pₙ, r) and p_k > 0, then the sequence
{ζ_k(p_q, r_q)} of the kth components of {ζ(p_q, r_q)} is bounded. Similarly, r ∈ (0, 1) implies
that the sequence {ζₙ₊₁(p_q, r_q)} is bounded."

**Formalization Note.** `(p, r)` is `π : Fin (n + 1) → ℝ` with goods `k.castSucc` and the rate
`Fin.last n`; `‖ζ‖₁ = ∑ₖ |ζₖ|` over all `n + 1` coordinates (p.20). "Bounded" is
`∃ C, ∀ q, |·| ≤ C`. `ζ` is `excessDemand` for any family solving the agents' problem on `P`.
Endowments are `Spread` (reading R1); with a singleton support (i) is false. -/
theorem lemma_8 {n : ℕ} (E : Economy n) (hA : Assumption1 E) (hS : Spread E)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (V g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (hF : IsEqFamily E x V g μ) :
    (∀ (πs : ℕ → Fin (n + 1) → ℝ) (π : Fin (n + 1) → ℝ),
      (∀ q, πs q ∈ interiorPrices n) → Tendsto πs atTop (𝓝 π) →
      π ∈ priceSimplex n → π ∉ interiorPrices n → (∃ k : Fin n, 0 < π k.castSucc) →
      Tendsto (fun q => ∑ k, |excessDemand E x g μ (πs q) k|) atTop atTop) ∧
    (∀ (πs : ℕ → Fin (n + 1) → ℝ) (π : Fin (n + 1) → ℝ),
      (∀ q, πs q ∈ interiorPrices n) → Tendsto πs atTop (𝓝 π) →
      (∀ k : Fin n, 0 < π k.castSucc →
        ∃ C : ℝ, ∀ q, |excessDemand E x g μ (πs q) k.castSucc| ≤ C) ∧
      (0 < π (Fin.last n) → π (Fin.last n) < 1 →
        ∃ C : ℝ, ∀ q, |excessDemand E x g μ (πs q) (Fin.last n)| ≤ C)) := by sorry

end BewleyGE
