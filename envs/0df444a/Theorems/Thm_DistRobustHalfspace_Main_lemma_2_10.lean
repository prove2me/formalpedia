-- Prove2me | Theorems.Thm_DistRobustHalfspace_Main_lemma_2_10
-- name    : DistRobustHalfspace.Main.lemma_2_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:18:24.74099+00:00
-- url     : https://prove2.me/theorems/67c2fba0-4f8c-40c8-b8c2-724531a737d4
-- title:
--   Lemma 2.10 — distance disagreement in the YES case: DD ≤ 3Δ + 3ξ²(1 + (|t̂|+ξ)/τ(t̂))²
-- statement:
--   Let $f$ be a halfspace and $D=\mathcal N(0,I_n)$. Let $\xi\ge0$ and let $\hat t$ be a $\xi$-good threshold estimate for $f$. Let $\Delta\ge0$ and let $\beta:\mathbb R^n\to\mathbb R$ be bounded and measurable with
--   $$\mathbb E_{x\sim\mathcal N(0,I_n)}\big[(\alpha_f(x)-\beta(x))^2\big]\le\Delta.\qquad(8)$$
--   Then
--   $$\mathrm{DD}^{\hat t}_\beta(f,D)\ \le\ 3\Delta+3\xi^2\Big(1+\frac{|\hat t|+\xi}{\tau(\hat t)}\Big)^2.$$
--
--   Differences from the source:
--   - generalization: standing assumption n ≥ n₀ of §§2–3 → every dimension n; reason: the statement is dimension-free; it specializes to n ≥ n₀
--   - reading: "f is a halfspace ... t̂ is a ξ-good threshold estimate for f" → `IsGoodThreshold f ξ t̂`: f = sgn(⟨x, v⟩ − t) with ‖v‖ = 1 and |t − t̂| ≤ ξ; reason: Definition 2.4 defines ξ-good only for unit-normal halfspaces, so the hypothesis already says f is one
--   - encoding: E_{x∼N(0,Iₙ)}[(α_f(x) − β(x))²] ≤ Δ (8) → `∫⁻ ofReal(((localDist f x).toReal − β x)²) dN(0, Iₙ) ≤ ofReal Δ`; reason: α_f is extended-real; for a unit-normal halfspace ℓ_f ∈ [1/2, 1) so α_f is finite and `toReal` is exact; a lower integral cannot vanish by non-integrability
--   - encoding: DD^{t̂}_β(f, D) = E_{y∼D}[(f(y)(⟨y, E[ṽ(t̂)]⟩ − t̂) − β(y))²] → `DD β t̂ f D : ℝ≥0∞`, a lower Lebesgue integral of the nonnegative integrand; reason: the expectation of a nonnegative function, +∞ when not integrable, never a junk 0
--   - reading: sign(⟨w, x⟩ − t) with sign(0) unspecified → `sgn 0 = 1` (sign(0) = +1); reason: the paper never fixes sign(0); a {±1}-valued sign needs a value there
--   - encoding: ℝⁿ → `Rn n = EuclideanSpace ℝ (Fin n)`; reason: Lean's Euclidean ℝⁿ with its Borel σ-algebra
-- source:
--   Xi Chen, Renato Ferreira Pinto Jr., Nathaniel Harms, Rocco A. Servedio, Distribution-Robust Halfspace Testing, 2026 (STOC 2027 submission manuscript, sha256 545c331d…1018a87), Lemma 2.10, p. 15 (PDF 17)

import Mathlib
import Definitions.Def_DistRobustHalfspace_Main_Testers
import Definitions.Def_DistRobustHalfspace_Main_Estimators
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace DistRobustHalfspace.Main

/-- Lemma 2.10 (p. 15): YES case of the distance disagreement measure. `D = N(0, Iₙ)`, `t̂` a
`ξ`-good threshold estimate for the halfspace `f`, `β` bounded measurable with
`E_{x∼N(0,Iₙ)}[(α_f(x) − β(x))²] ≤ Δ` (8). Then `DD^{t̂}_β(f, D) ≤ 3Δ + 3ξ²(1 + (|t̂| + ξ)/τ(t̂))²`. -/
theorem lemma_2_10 {n : ℕ} (f : Rn n → ℝ) (ξ t' : ℝ) (hξ : 0 ≤ ξ)
    (hgood : IsGoodThreshold f ξ t') (Δ : ℝ) (hΔ : 0 ≤ Δ) (β : Rn n → ℝ)
    (hβm : Measurable β) (hβb : ∃ M : ℝ, ∀ x, |β x| ≤ M)
    (h8 : ∫⁻ x, ENNReal.ofReal (((localDist f x).toReal - β x) ^ 2) ∂(stdGaussian (Rn n))
      ≤ ENNReal.ofReal Δ) :
    DD β t' f (stdGaussian (Rn n)) ≤
      ENNReal.ofReal (3 * Δ + 3 * ξ ^ 2 * (1 + (|t'| + ξ) / tau t') ^ 2) := by sorry

end DistRobustHalfspace.Main
