-- Prove2me | Theorems.Thm_BosonicLearn_eq_210
-- name    : BosonicLearn.eq_210
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:15:26.834907+00:00
-- url     : https://prove2.me/theorems/6ad1a9b1-6f58-467e-961f-30ef5f200294
-- title:
--   Eq. (210) — concentration of the empirical mean and centered covariance of $N$ Gaussian samples
-- statement:
--   Let $C\in\mathbb R^{2n\times2n}$ be positive definite, $\mu\in\mathbb R^{2n}$, $N\ge1$, $\delta\in(0,1)$, and let $Y_1,\dots,Y_N$ be i.i.d. $\mathcal N(\mu,C)$. Put
--
--   $$\hat\mu=\frac1N\sum_{j}Y_j,\qquad \hat C=\frac1N\sum_j(Y_j-\hat\mu)(Y_j-\hat\mu)^T,\qquad \chi=\sqrt{2n}+\sqrt{2\log(2/\delta)},\qquad \zeta=\frac{2\chi}{\sqrt N}+\frac{2\chi^2}{N}.$$
--
--   Then with probability at least $1-\delta$ both
--
--   $$\big\|C^{-1/2}(\hat\mu-\mu)\big\|_2\le\frac{\chi}{\sqrt N}\qquad\text{and}\qquad (1-\zeta)C\preceq\hat C\preceq(1+\zeta)C$$
--
--   hold. This is the classical estimation step of heterodyne tomography (Theorem 8); the paper takes it from [BMEM25, Lemma 9].
--
--   Differences from the source:
--   - generalization: C = Σ + ½I, the covariance of heterodyne outcomes of a Gaussian state → every positive definite covariance C on ℝ^{2n}; reason: the bound is a statement about Gaussian samples and the proof uses only C ≻ 0; C = Σ + ½I is positive definite
--   - encoding: ‖C^{-1/2}(µ̂ − µ)‖₂ ≤ χ/√N → (µ̂ − µ)ᵀ C⁻¹ (µ̂ − µ) ≤ χ²/N; reason: equivalent for C ≻ 0; avoids a matrix square root
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §7.2, Eqs. (208)–(210), p. 61

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Eq. (210) — mean and covariance concentration for `N` Gaussian samples.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.2, proof of Theorem 8, Eqs. (208)–(210), p. 61: "From N independent heterodyne outcomes Y_1, …, Y_N,
define the empirical mean and the centered empirical covariance by µ̂ := (1/N) Σ_j Y_j, Ĉ := (1/N) Σ_j (Y_j − µ̂)(Y_j − µ̂)^T.
… Set χ := √(2n) + √(2 log(2/δ)), ζ := 2χ/√N + 2χ²/N. The Gaussian concentration bound of [BMEM25, Lemma 9, Eqs.
(91), (94), and (95)] implies that, with probability at least 1 − δ, ‖C^{−1/2}(µ̂ − µ)‖_2 ≤ χ/√N,
(1 − ζ)C ⪯ Ĉ ⪯ (1 + ζ)C."

Let `C` be a positive definite `2n × 2n` matrix, `µ ∈ ℝ²ⁿ`, `N ≥ 1`, `δ ∈ (0, 1)`, and `Y₁, …, Y_N` i.i.d. `N(µ, C)`.
Then with probability at least `1 − δ` both `(µ̂ − µ)ᵀ C⁻¹ (µ̂ − µ) ≤ χ²/N` and `(1 − ζ)C ⪯ Ĉ ⪯ (1 + ζ)C` hold.

**Formalization Note.** `‖C^{−1/2} v‖₂ ≤ χ/√N` is written in the equivalent squared form `vᵀC⁻¹v ≤ χ²/N`
(`C ≻ 0`). Loewner order is positive semidefiniteness of the difference. Classical statement, imported by the
paper from [BMEM25]. -/
theorem eq_210 {n : ℕ} (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (μ : Fin n ⊕ Fin n → ℝ) (C : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (hC : C.PosDef) :
    let χ : ℝ := Real.sqrt (2 * n) + Real.sqrt (2 * Real.log (2 / δ))
    let ζ : ℝ := 2 * χ / Real.sqrt N + 2 * χ ^ 2 / N
    ENNReal.ofReal (1 - δ) ≤
      (Measure.pi fun _ : Fin N => multivariateGaussian (WithLp.toLp 2 μ) C)
        {Y | let μhat : Fin n ⊕ Fin n → ℝ := fun a => (1 / (N : ℝ)) * ∑ j, WithLp.ofLp (Y j) a
              let Chat : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := Matrix.of fun a b =>
                (1 / (N : ℝ)) * ∑ j, (WithLp.ofLp (Y j) a - μhat a) * (WithLp.ofLp (Y j) b - μhat b)
              (μhat - μ) ⬝ᵥ (C⁻¹ *ᵥ (μhat - μ)) ≤ χ ^ 2 / N ∧
                (Chat - (1 - ζ) • C).PosSemidef ∧ ((1 + ζ) • C - Chat).PosSemidef} := by sorry

end BosonicLearn
