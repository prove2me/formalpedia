-- Prove2me | Theorems.Thm_BosonicLearn_gaussian_bilinear_exp_bound
-- name    : BosonicLearn.gaussian_bilinear_exp_bound
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-14T02:24:58.056546+00:00
-- url     : https://prove2.me/theorems/e6ff4c09-e702-4e33-9cea-d13270b861f7
-- title:
--   A Gaussian chaos bound: $\mathbb E\exp(g^TMg')\le1+\mathrm{Tr}M^2$ for independent standard Gaussian vectors when $\mathrm{Tr}M^2\le\frac12$
-- statement:
--   The classical Gaussian integral that produces the square of the relative covariance error in a $\chi^2$ proof of Theorem 7.
--
--   Let $g,g'$ be independent standard Gaussian vectors in $\mathbb R^d$ and $M$ a real symmetric $d\times d$ matrix with $\operatorname{Tr}M^2\le\frac12$. Then $\exp(g^TMg')$ is integrable and
--
--   $$\mathbb E\exp(g^TMg')\le1+\operatorname{Tr}M^2 .$$
--
--   The exact value is $\det(\mathbf 1-M^2)^{-1/2}$. Proof idea: integrating out $g'$ gives $\exp(\frac12|Mg|^2)$; writing $|Mg|^2=\sum_kt_k\langle o_k,g\rangle^2$ with unit vectors $o_k$ and $\sum_kt_k=T:=\operatorname{Tr}M^2$, Jensen's inequality gives $\mathbb E\exp(\frac12|Mg|^2)\le(1-T)^{-1/2}\le1+T$.
--
--   **Formalization Note** The measure is `stdGaussian (EuclideanSpace ℝ ι)` and its product with itself.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §7.1, Theorem 7, Eqs. (184)–(185), p. 55

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace BosonicLearn

/-- **A Gaussian chaos bound: `𝔼 exp(gᵀ M g′) ≤ 1 + Tr M²` when `Tr M² ≤ ½`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.1, Theorem 7, Eqs. (184)–(185), p. 55 (the bound is quadratic in the relative covariance error `Δ_rel`); this is the
classical Gaussian integral that produces `Δ_rel²` in a `χ²` proof of that bound.

Let `g, g′` be independent standard Gaussian vectors in `ℝ^ι` and `M` a real symmetric matrix with
`Tr M² ≤ ½`. Then `exp(gᵀ M g′)` is integrable and `𝔼 exp(gᵀ M g′) ≤ 1 + Tr M²`.

**Formalization Note.** The exact value is `det(1 − M²)^{−1/2}`. Integrating out `g′` gives `exp(½|Mg|²)`; writing
`|Mg|² = ∑ₖ t_k ⟨o_k, g⟩²` with unit vectors `o_k` (the normalized rows) and `∑ t_k = Tr M² =: T`, Jensen's
inequality gives `𝔼 exp(½|Mg|²) ≤ (1 − T)^{−1/2} ≤ 1 + T`. -/
theorem gaussian_bilinear_exp_bound {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ)
    (hM : M.IsSymm) (hT : (M * M).trace ≤ 1 / 2) :
    Integrable (fun q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι =>
        Real.exp (∑ i, ∑ j, q.1 i * M i j * q.2 j))
      ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) ∧
    ∫ q : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι, Real.exp (∑ i, ∑ j, q.1 i * M i j * q.2 j)
        ∂((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))) ≤
      1 + (M * M).trace := by sorry

end BosonicLearn
