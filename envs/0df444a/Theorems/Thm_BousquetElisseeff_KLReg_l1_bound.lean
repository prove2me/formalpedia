-- Prove2me | Theorems.Thm_BousquetElisseeff_KLReg_l1_bound
-- name    : BousquetElisseeff.KLReg.l1_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:46:17.670739+00:00
-- url     : https://prove2.me/theorems/84086313-76c7-460e-a7d8-14a2b6054365
-- title:
--   $L^1$ stability of the posterior: $\int_\Theta |f - f^{\setminus i}| \le \frac{M}{\lambda m}$
-- statement:
--   Let $\mu$ be a reference measure on a measurable space $\Theta$ and let $\mathcal F$ be the set of probability densities with respect to $\mu$. Let $r(\theta, z)$ be the base loss of the hypothesis $h_\theta$ on the example $z$, measurable in $\theta$, with $0 \le r(\theta,z) \le M$. For $g \in \mathcal F$ write $\ell(g,z) = \int_\Theta r(\theta,z)\,g(\theta)\,d\mu(\theta)$ (eq. (28)) and $K(g,g') = \int_\Theta g \ln(g/g')\,d\mu \in [0,\infty]$ for the relative entropy. Fix a prior $f_0 \in \mathcal F$, a parameter $\lambda > 0$, a sample $S = (z_1,\dots,z_m)$ and an index $i \in \{1,\dots,m\}$. Let $f$ be any minimizer over $\mathcal F$ of
--   $$R_r(g) = \frac1m \sum_{j=1}^m \ell(g,z_j) + \lambda K(g,f_0) \qquad (19) = (29),$$
--   and let $f^{\setminus i}$ be any minimizer over $\mathcal F$ of
--   $$R_r^{\setminus i}(g) = \frac1m \sum_{j\ne i} \ell(g,z_j) + \lambda K(g,f_0). \qquad (20)$$
--
--   Then
--   $$\int_\Theta |f(\theta) - f^{\setminus i}(\theta)|\, d\mu(\theta) \le \frac{M}{\lambda m}.$$
--
--   Removing one training point moves the regularized posterior by at most $M/(\lambda m)$ in $L^1$. Besides giving Theorem 24, this bound yields the classification stability $M/(\lambda m)$ stated in the remark after Theorem 24.
--
--   Differences from the source:
--   - generalization: standing assumption "all sets are countable" (p. 501) → Θ any measurable space, Z any type, μ any measure; reason: no step of the argument uses countability; the countable case is an instance
--   - encoding: r a loss on 𝓗 × 𝓩 bounded by M (p. 518), costs nonnegative (p. 502), functions measurable (p. 501) → r : Θ → Z → ℝ with θ ↦ r θ z measurable and 0 ≤ r θ z ≤ M; reason: r(h_θ, z) depends on h only through θ; the bounds are the paper's standing nonnegative costs and its bound M
--   - encoding: regularization parameter λ (unqualified) → 0 < lam; reason: the objective and the bound M²/(λm) presuppose λ > 0
--   - encoding: f a minimizer of (19), f^{\i} a minimizer of (20) (Lemma 20, pp. 512–513) → IsKLRegMinimizer with weight 1/m over univ (f) and over univ.erase i (f′); reason: literal transcription of (19) and (20) with N = K(·, f₀)
--   - encoding: 𝓕 = probability distributions dominated by the reference measure, given by their densities (p. 517) → IsDensity μ g: g measurable, g ≥ 0, ∫ g dμ = 1; reason: this is the paper's 𝓕; densities equal μ-a.e. give the same ℓ and K
--   - encoding: K(g, g′) = ∫_Θ g ln(g/g′) dθ (p. 517) → relEnt μ g g′ = klDiv (g·μ) (g′·μ) ∈ [0, ∞]; reason: for probability measures Mathlib's klDiv is ∫ g ln(g/g′) when finite and +∞ otherwise; same values
-- source:
--   Bousquet & Elisseeff, Stability and Generalization, JMLR 2 (2002) 499–526, proof of Theorem 24, unnumbered display, p. 518 (reused in the remark after the proof, p. 518)

import Mathlib
import Definitions.Def_BousquetElisseeff_KLReg_IsDensity
import Definitions.Def_BousquetElisseeff_KLReg_relEnt
import Definitions.Def_BousquetElisseeff_KLReg_avgLoss
import Definitions.Def_BousquetElisseeff_KLReg_IsKLRegMinimizer

open MeasureTheory

namespace BousquetElisseeff.KLReg

/-- **L¹ bound between f and f^{\i}** (proof of Theorem 24).
Bousquet & Elisseeff, *Stability and Generalization*, JMLR 2 (2002) 499–526, proof of Theorem 24, unnumbered display, p. 518: "hence ∫_Θ |f(θ) − f^{\i}(θ)|dθ ≤ M/(λm),"
(reused in the remark after the proof, p. 518, for classification stability).

Setting (all items): `μ` is a reference measure on a measurable space Θ, `r θ z` the base loss
r(h_θ, z), measurable in θ with `0 ≤ r ≤ M` (nonnegative costs, p. 502; bound M, p. 518),
`λ > 0`, `f₀` a density (the prior), `S : Fin m → Z` the sample z₁, …, z_m, `i` an index, and
`f` any minimizer over 𝓕 of (19) = (29): `(1/m) Σ_{j} ℓ(g, z_j) + λK(g, f₀)`.
For every minimizer `f'` over 𝓕 of (20), `(1/m) Σ_{j ≠ i} ℓ(g, z_j) + λK(g, f₀)` (the paper's
f^{\i}), `∫ |f − f′| dμ ≤ M/(λm)`. -/
theorem l1_bound {Θ Z : Type*} [MeasurableSpace Θ] (μ : Measure Θ) (r : Θ → Z → ℝ)
    (M lam : ℝ) (f0 : Θ → ℝ) (hr_meas : ∀ z, Measurable (fun θ => r θ z))
    (hr : ∀ θ z, 0 ≤ r θ z ∧ r θ z ≤ M) (hlam : 0 < lam) (hf0 : IsDensity μ f0)
    {m : ℕ} (S : Fin m → Z) (i : Fin m) (f : Θ → ℝ)
    (hf : IsKLRegMinimizer μ r f0 lam (1 / (m : ℝ)) Finset.univ S f)
    (f' : Θ → ℝ)
    (hf' : IsKLRegMinimizer μ r f0 lam (1 / (m : ℝ)) (Finset.univ.erase i) S f') :
    ∫ θ, |f θ - f' θ| ∂μ ≤ M / (lam * (m : ℝ)) := by sorry

end BousquetElisseeff.KLReg
