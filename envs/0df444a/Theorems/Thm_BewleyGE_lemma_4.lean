-- Prove2me | Theorems.Thm_BewleyGE_lemma_4
-- name    : BewleyGE.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:36:03.35983+00:00
-- url     : https://prove2.me/theorems/adc513eb-7e23-40fe-83c2-bdf815214040
-- title:
--   Lemma 4 (corrected: spread endowments) — the invariant distribution is weakly continuous in prices
-- statement:
--   Let the economy satisfy Assumption 1 and have a spread endowment support, and let $(x^*,V,g,\mu)$ solve the agents' problem at every $(p,r)\in P$. If $(p_q,r_q)\in P$ converges to $(p,r)\in P$, then
--   $$
--   \mu(\cdot;p_q,r_q)\ \Rightarrow\ \mu(\cdot;p,r)\qquad\text{weakly.}
--   $$
--
--   The state spaces $A(p_q,r_q)$ move with the prices, which is why the statement is about measures on $\mathbb R$.
--
--   Differences from the source:
--   - correction: the §2 endowment model: 𝒴 = 𝒴₁ × ⋯ × 𝒴ₙ with a strict top element y′, which for n ≥ 2 forces 𝒴 to be a single point → a finite set 𝒴 of strictly positive vectors with e > 0, satisfying Spread (y″ ≪ y′ for some y′, y″ ∈ 𝒴); reason: for a singleton 𝒴 = {y₀}, r = 1/β − 1 and any p ≫ 0 on P, every point mass at a ∈ A(p, r) is invariant, so Lemma 2's uniqueness fails and ζ is undefined; the proof of Lemma 8 (pp.26–27) uses exactly the gap that Spread provides
--   - reading: Assumption 1: U continuously differentiable with ∂U(0)/∂xⱼ = ∞; u_p continuously differentiable → U continuous on ℝⁿ₊ and C¹ on the open orthant, (U(t eⱼ) − U(0))/t → ∞ as t ↓ 0; u_p C¹ on (0, ∞); reason: C¹ on the closed orthant contradicts ∂U(0)/∂xⱼ = ∞ and excludes the paper's CES example; u_p′(0+) = ∞ excludes C¹ at 0
--   - reading: U strictly increasing: x > x′ implies U(x) > U(x′), with x > x′ undefined → x′ ≤ x coordinatewise and x′ ≠ x imply U(x′) < U(x); reason: the paper defines only x ≥ x′; the proof of Lemma 8 (p.27) uses this reading
--   - encoding: V(a) = sup over strategies of expected discounted utility (p.6) → V bounded on A(p, r) with TV = V and the maximum attained; reason: the paper's own characterization of V as the unique bounded fixed point of T (p.7, footnote 10)
--   - encoding: μ ∈ P(A(p, r)); integrals over A(p, r) → probability measures on ℝ with μ(A(p, r)ᶜ) = 0; set integrals over A(p, r); reason: the same objects
--   - encoding: ζ built from the unique g(·, p, r), x*(·, p), μ(·; p, r) of Lemmas 1–2 → ζ built from any family (x, V, g, μ) that satisfies Definition 1(i)–(ii) at every point of P; reason: by Lemmas 1–2 every such family agrees with the paper's objects on A(p, r), so ζ is the paper's; no choice function enters
--   - encoding: g(·, p, r) defined on A(p, r), with no regularity stated in (1) → the savings policy is a measurable function on ℝ (values off A(p, r) otherwise free); reason: the paper's g is continuous on the compact A(p, r) (Lemma 1), so it has measurable extensions, and the wealth operator only sees g on A(p, r); measurability keeps the image measures of (2) from being zero
--   - encoding: (p, r) ∈ ℝⁿ × ℝ, with p_{n+1} := r on p.29 → π : Fin (n + 1) → ℝ, goods i.castSucc, rate Fin.last n; reason: the paper's own convention
--   - encoding: μ(pₙ, rₙ) converges weakly to μ(p, r) → ∫ f dμ(pₙ, rₙ) → ∫ f dμ(p, r) for every bounded continuous f; reason: the definition of weak convergence
-- source:
--   Light, General equilibrium in a heterogeneous-agent incomplete-market economy, arXiv:1906.06810v2, Lemma 4, p.23

import Mathlib
import Definitions.Def_BewleyGE_Assumption1
import Definitions.Def_BewleyGE_Spread
import Definitions.Def_BewleyGE_IsEqFamily
import Definitions.Def_BewleyGE_WeakConv

open MeasureTheory Filter Topology

namespace BewleyGE

/-- **Lemma 4 (continuity of the invariant distribution).** Light, arXiv:1906.06810v2, Lemma 4,
p.23: "The unique invariant wealth distribution μ is continuous in (p, r) on P, i.e., if
{pₙ, rₙ} converges to (p, r), then μ(pₙ, rₙ) converges weakly to μ(p, r)."

**Formalization Note.** `(x, V, g, μ)` is any family solving the agents' problem with an
invariant distribution at every `π = (p, r) ∈ P` (`IsEqFamily`); by Lemmas 1–2 it is the paper's.
The sequence and its limit lie in `P`. Endowments are `Spread` (reading R1). -/
theorem lemma_4 {n : ℕ} (E : Economy n) (hA : Assumption1 E) (hS : Spread E)
    (x : (Fin (n + 1) → ℝ) → ℝ → Fin n → ℝ) (V g : (Fin (n + 1) → ℝ) → ℝ → ℝ)
    (μ : (Fin (n + 1) → ℝ) → Measure ℝ) (hF : IsEqFamily E x V g μ)
    (πs : ℕ → Fin (n + 1) → ℝ) (π : Fin (n + 1) → ℝ)
    (hπs : ∀ q, πs q ∈ interiorPrices n) (hπ : π ∈ interiorPrices n)
    (hlim : Tendsto πs atTop (𝓝 π)) :
    WeakConv (fun q => μ (πs q)) (μ π) := by sorry

end BewleyGE
