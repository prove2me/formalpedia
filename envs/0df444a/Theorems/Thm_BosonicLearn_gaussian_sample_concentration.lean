-- Prove2me | Theorems.Thm_BosonicLearn_gaussian_sample_concentration
-- name    : BosonicLearn.gaussian_sample_concentration
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T18:03:25.219044+00:00
-- url     : https://prove2.me/theorems/0f6b0d01-e0ea-43f7-9873-ce08e95b8b5f
-- title:
--   Gaussian samples: $\|C^{-1/2}(\hat\mu-\mu)\|\le\chi/\sqrt N$ and $(1-\zeta)C\preceq\hat C\preceq(1+\zeta)C$ with probability $\ge1-3e^{-t^2/2}$
-- statement:
--   Mean and covariance of $N$ Gaussian samples concentrate in relative (whitened) form, with failure probability $3e^{-t^2/2}$.
--
--   Let $C$ be a positive definite $2n\times2n$ real matrix, $\mu\in\mathbb R^{2n}$, $N\ge1$ and $t\ge0$. Put
--
--   $$
--   \chi=\sqrt{2n}+t,\qquad \zeta=\frac{2\chi}{\sqrt N}+\frac{2\chi^2}{N}.
--   $$
--
--   Let $Y_1,\dots,Y_N$ be i.i.d. $\mathcal N(\mu,C)$, $\hat\mu=\frac1N\sum_jY_j$ and $\hat C=\frac1N\sum_j(Y_j-\hat\mu)(Y_j-\hat\mu)^\top$. Then with probability at least $1-3e^{-t^2/2}$, simultaneously
--
--   $$
--   (\hat\mu-\mu)^\top C^{-1}(\hat\mu-\mu)\le\frac{\chi^2}{N}\qquad\text{and}\qquad(1-\zeta)\,C\preceq\hat C\preceq(1+\zeta)\,C .
--   $$
--
--   Relation to Eq. (210). This is the event of Eq. (210) (`BosonicLearn.eq_210`) with the deviation parameter $t$ left free. The three terms of the failure probability come from the norm of the whitened sample mean and from the smallest and largest singular values of the whitened $N\times2n$ data matrix. Taking $t=\sqrt{2\log(3/\delta)}$ gives probability at least $1-\delta$; taking $t=\sqrt{2\log(2/\delta)}$, the choice of Eq. (209), this argument gives $1-\tfrac32\delta$. For the proof of Theorem 8 the difference only changes the universal constant.
--
--   Role. It replaces `BosonicLearn.eq_210` in the proof of Theorem 8 (heterodyne tomography), where $C=\Sigma+\tfrac12\mathbf 1$ is the covariance of the heterodyne outcomes.
--
--   **Formalization Note** Same event set as `eq_210`: samples are `Measure.pi fun _ : Fin N => multivariateGaussian (WithLp.toLp 2 μ) C` on `EuclideanSpace ℝ (Fin n ⊕ Fin n)`, Loewner order is `Matrix.PosSemidef` of the difference, and the first inequality is the squared form of $\|C^{-1/2}(\hat\mu-\mu)\|_2\le\chi/\sqrt N$. The bound is `1 - ENNReal.ofReal (3 * exp (-t^2/2))`. The proof imports the proved theorems `GaussianMatrix.extreme_singular_values_deviation`, `GaussianMatrix.gaussian_concentration` and `GaussianMatrix.frobenius_second_moment` of the mission series on Gaussian random matrices.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §7.2, proof of Theorem 8, Eqs. (208)–(210), p. 61 (mean and covariance concentration, [BMEM25, Lemma 9])

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Mean and covariance concentration for `N` Gaussian samples, with failure probability `3e^{−t²/2}`.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.2, proof of Theorem 8, Eqs. (208)–(210), p. 61: "Set χ := √(2n) + √(2 log(2/δ)), ζ := 2χ/√N + 2χ²/N. The
Gaussian concentration bound of [BMEM25, Lemma 9, Eqs. (91), (94), and (95)] implies that, with probability at
least 1 − δ, ‖C^{−1/2}(µ̂ − µ)‖_2 ≤ χ/√N, (1 − ζ)C ⪯ Ĉ ⪯ (1 + ζ)C."

Let `C` be a positive definite `2n × 2n` matrix, `µ ∈ ℝ²ⁿ`, `N ≥ 1`, `t ≥ 0`, `χ = √(2n) + t`,
`ζ = 2χ/√N + 2χ²/N`, and `Y₁, …, Y_N` i.i.d. `N(µ, C)` with empirical mean `µ̂` and centered empirical
covariance `Ĉ`. Then with probability at least `1 − 3e^{−t²/2}` both
`(µ̂ − µ)ᵀ C⁻¹ (µ̂ − µ) ≤ χ²/N` and `(1 − ζ)C ⪯ Ĉ ⪯ (1 + ζ)C` hold.

**Formalization Note.** Same event as `eq_210`, with the deviation parameter `t` free and the failure
probability `3e^{−t²/2}`: one term for the norm of the whitened sample mean and two for the extreme singular
values of the whitened data matrix. Taking `t = √(2 log(3/δ))` gives probability at least `1 − δ`; with
`t = √(2 log(2/δ))` as in Eq. (209) this argument gives `1 − 3δ/2`. -/
theorem gaussian_sample_concentration {n : ℕ} (N : ℕ) (hN : 1 ≤ N) (t : ℝ) (ht : 0 ≤ t)
    (μ : Fin n ⊕ Fin n → ℝ) (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hC : C.PosDef) :
    let χ : ℝ := Real.sqrt (2 * n) + t
    let ζ : ℝ := 2 * χ / Real.sqrt N + 2 * χ ^ 2 / N
    1 - ENNReal.ofReal (3 * Real.exp (-t ^ 2 / 2)) ≤
      (Measure.pi fun _ : Fin N => multivariateGaussian (WithLp.toLp 2 μ) C)
        {Y | let μhat : Fin n ⊕ Fin n → ℝ := fun a => (1 / (N : ℝ)) * ∑ j, WithLp.ofLp (Y j) a
              let Chat : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := Matrix.of fun a b =>
                (1 / (N : ℝ)) * ∑ j, (WithLp.ofLp (Y j) a - μhat a) * (WithLp.ofLp (Y j) b - μhat b)
              (μhat - μ) ⬝ᵥ (C⁻¹ *ᵥ (μhat - μ)) ≤ χ ^ 2 / N ∧
                (Chat - (1 - ζ) • C).PosSemidef ∧ ((1 + ζ) • C - Chat).PosSemidef} := by sorry

end BosonicLearn
