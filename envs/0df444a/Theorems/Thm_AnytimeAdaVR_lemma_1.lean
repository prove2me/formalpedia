-- Prove2me | Theorems.Thm_AnytimeAdaVR_lemma_1
-- name    : AnytimeAdaVR.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:27:51.058136+00:00
-- url     : https://prove2.me/theorems/b41ce8c1-d406-4826-8e41-4a5593cfc9d1
-- title:
--   Lemma 1 — validation adds at most $\sqrt6\,\sigma/\sqrt n$
-- statement:
--   Suppose the oracle satisfies Assumption 2 with variance bound $\sigma^2$. Let $X_S,X_M,X_D$ be random points of $\mathbb R^d$ with finite expected gradient norm, chosen before validation, and let $n\ge1$. For each $i$, draw $n$ fresh samples $\xi_{i,1},\dots,\xi_{i,n}$ (independent of each other and of the candidates) and form
--   $$
--   \hat g_i=\frac1n\sum_{s=1}^n g(X_i;\xi_{i,s}).
--   $$
--   If $\hat x=X_{\hat\imath}$, where $\hat\imath$ minimizes $\|\hat g_i\|$, then
--   $$
--   \mathbb E\,\|\nabla f(\hat x)\|\le\min_{i\in\{S,M,D\}}\mathbb E\,\|\nabla f(X_i)\|+\frac{\sqrt6\,\sigma}{\sqrt n}.
--   $$
--   The candidates need not be independent of each other. Lemma 1 lets the algorithm select among its three paths without knowing $\sigma$ or which path has the best guarantee.
--
--   **Formalization Note** The selection may be any rule with measurable level sets that returns a minimizer of $\|\hat g_i\|$; the paper's tie order S, M, D is one.
--
--   Differences from the source:
--   - encoding: ℝ^d with the Euclidean norm → EuclideanSpace ℝ (Fin d); reason: Mathlib's Euclidean space carries the Euclidean norm; same instances
--   - encoding: expectations E‖·‖ of nonnegative quantities → lower integrals ∫⁻ of ‖·‖ₑ in ℝ≥0∞, compared with ENNReal.ofReal of the bound; reason: the lower integral is the expectation of a nonnegative quantity and never a junk value; same instances
--   - encoding: a stochastic gradient g(x; ξ) queried at adaptively chosen points → hypothesis Measurable (Function.uncurry g); reason: needed for the iterates at adaptive points to be random variables, so that the paper's expectations are defined; it excludes only oracles for which they are undefined
--   - encoding: candidates with finite expected gradient norm, chosen before validation; n fresh gradients at each candidate → measurable X_i with ∫⁻‖∇f(X_i)‖ₑ < ⊤; measurable validation samples with law μ, mutually independent and independent of the vector (X_S, X_M, X_D); reason: the paper's 'fresh' and 'chosen before validation'; no independence among the candidates is assumed, as on p.27
--   - generalization: return the candidate with the smallest norm of the average (ties in the order S, M, D) → any selection rule with measurable level sets that returns a minimizer of the norm of the validation mean; reason: the paper's tie rule is one such selection, so the statement specializes to it
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §3, Lemma 1, eq. (8), p.6; proof App. A.5, p.15

import Mathlib
import Definitions.Def_AnytimeAdaVR_Path
import Definitions.Def_AnytimeAdaVR_Assumption2

namespace AnytimeAdaVR

open MeasureTheory ProbabilityTheory

/-- **Lemma 1 (Validation).** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §3, p.6, eq. (8): "Let X_S, X_M, X_D be any three
candidates with finite expected gradient norm, chosen before validation. Average n fresh gradients
at each candidate and return the one with the smallest norm of this average. Under Assumption 2,
E‖∇f(x̂)‖ ≤ min_{i∈{S,M,D}} E‖∇f(X_i)‖ + √6σ/√n."

The candidates `X i` are random vectors on a probability space `(Ω, P)`; the validation samples
`ζ i j` (`j < n`) have the oracle's law `μ`, are mutually independent, and are independent of the
candidates (as one random vector); the candidates need not be independent of each other. `sel` is
any selection rule that returns an index minimizing the norm of the validation mean.

**Formalization Note.** Expectations of norms are lower integrals of `‖·‖ₑ`. "Finite expected
gradient norm" is `∫⁻ ‖∇f(X i)‖ₑ < ⊤`. "Chosen before validation" is the independence of the
candidates from the validation samples. The selection may break ties in any measurable way; the
paper's order S, M, D is one such rule. The stochastic gradient is jointly measurable. -/
theorem lemma_1 {d : ℕ} {Ξ : Type*} [MeasurableSpace Ξ] {μ : Measure Ξ} [IsProbabilityMeasure μ]
    {f : EuclideanSpace ℝ (Fin d) → ℝ}
    {g : EuclideanSpace ℝ (Fin d) → Ξ → EuclideanSpace ℝ (Fin d)} {σ : ℝ}
    (hg : Measurable (Function.uncurry g)) (hA2 : Assumption2 f g μ σ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n)
    (X : Path → Ω → EuclideanSpace ℝ (Fin d)) (hX : ∀ i, Measurable (X i))
    (hXfin : ∀ i, ∫⁻ ω, ‖gradient f (X i ω)‖ₑ ∂P < ⊤)
    (ζ : Path → Fin n → Ω → Ξ) (hζ : ∀ i j, Measurable (ζ i j))
    (hlaw : ∀ i j, P.map (ζ i j) = μ)
    (hindep : iIndepFun (fun p : Path × Fin n => ζ p.1 p.2) P)
    (hfresh : IndepFun (fun ω i => X i ω) (fun ω i j => ζ i j ω) P)
    (sel : Ω → Path) (hsel : ∀ i, MeasurableSet {ω | sel ω = i})
    (hmin : ∀ ω i,
      ‖((n : ℝ)⁻¹) • ∑ j, g (X (sel ω) ω) (ζ (sel ω) j ω)‖ ≤
        ‖((n : ℝ)⁻¹) • ∑ j, g (X i ω) (ζ i j ω)‖) :
    ∫⁻ ω, ‖gradient f (X (sel ω) ω)‖ₑ ∂P ≤
      (⨅ i, ∫⁻ ω, ‖gradient f (X i ω)‖ₑ ∂P) +
        ENNReal.ofReal (Real.sqrt 6 * σ / Real.sqrt n) := by sorry

end AnytimeAdaVR
