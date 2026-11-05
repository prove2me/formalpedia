-- Prove2me | Theorems.Thm_BrailovskayaVanHandel_prob_abs_norm_sub_gaussian_gt_le_and_abs_expect_norm_sub_le
-- name    : BrailovskayaVanHandel.prob_abs_norm_sub_gaussian_gt_le_and_abs_expect_norm_sub_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T01:22:39.701288+00:00
-- url     : https://prove2.me/theorems/77d6764c-a7bb-40bc-92e7-2ffdd07f734c
-- title:
--   Brailovskaya–van Handel, Corollary 2.7 — edge universality for the norm (finite uniform form)
-- statement:
--   There is a universal constant $C > 0$ with the following property. Let $D \ge 2$ and $n \ge 0$, let $\Omega$ be a finite nonempty set, let $Z_0 \in M_D(\mathbb C)$ be Hermitian, and let $Z_1, \dots, Z_n : \Omega \to M_D(\mathbb C)$ take Hermitian values with $\sum_{\omega \in \Omega} Z_i(\omega) = 0$ for each $i$. Draw $\omega = (\omega_1, \dots, \omega_n)$ uniformly from $\Omega^n$, so that the $Z_i(\omega_i)$ are independent, mean-zero, self-adjoint random matrices, and put $X = Z_0 + \sum_i Z_i(\omega_i)$. Let $G = Z_0 + \sum_{i \le n,\ \omega \in \Omega} g_{i\omega}\,|\Omega|^{-1/2} Z_i(\omega)$, where the $g_{i\omega}$ are i.i.d. real standard Gaussians. Then for every $t \ge 0$,
--   $$\mathbf P\big[\,\big|\|X\| - \mathbf E\|G\|\big| > C\varepsilon(t)\big] \le De^{-t},\qquad \varepsilon(t) = \sigma_*(X)\,t^{1/2} + R(X)^{1/3}\sigma(X)^{2/3}t^{2/3} + R(X)\,t,$$
--   and
--   $$\big|\mathbf E\|X\| - \mathbf E\|G\|\big| \le C\big(\sigma_*(X)(\log D)^{1/2} + R(X)^{1/3}\sigma(X)^{2/3}(\log D)^{2/3} + R(X)\log D\big).$$
--   Here $\|\cdot\|$ is the operator norm on $\ell^2$, and the parameters are those of Brailovskaya–van Handel §2.1.4 (p. 10): $\sigma(X) = \|\mathbf E[(X - \mathbf EX)^2]\|^{1/2}$, $\sigma_*(X) = \sup_{\|v\| = \|w\| = 1}\mathbf E\big[|\langle v, (X - \mathbf EX)w\rangle|^2\big]^{1/2}$, and $R(X) = \max_i \sup_\omega \|Z_i(\omega)\|$. Expectations and the probability over $\omega$ are uniform averages over $\Omega^n$, and $\mathbf E\|G\|$ is the integral against the standard Gaussian product measure on $\mathbb R^{\{1,\dots,n\} \times \Omega}$.
--
--   This is the norm form of Corollary 2.7 of T. Brailovskaya and R. van Handel, *Universality and sharp matrix concentration inequalities*, Geom. Funct. Anal. 34 (2024) 1734–1838, [doi:10.1007/s00039-024-00692-9](https://doi.org/10.1007/s00039-024-00692-9) (arXiv:2201.05142, p. 12): “*For any $t \ge 0$, we have $\mathbf P\big[|\lambda_{\max}(X) - \lambda_{\max}(G)| > C\varepsilon(t)\big] \le de^{-t}$, as well as $\mathbf P\big[|\lambda_{\max}(X) - \mathbf E\lambda_{\max}(G)| > C\varepsilon(t)\big] \le de^{-t}$, where $C$ is a universal constant and $\varepsilon(t)$ is as in Theorem 2.6. Moreover, $|\mathbf E\lambda_{\max}(X) - \mathbf E\lambda_{\max}(G)| \lesssim \sigma_*(X)(\log d)^{\frac12} + R(X)^{\frac13}\sigma(X)^{\frac23}(\log d)^{\frac23} + R(X)\log d$. The same bounds hold if $\lambda_{\max}(X), \lambda_{\max}(G)$ are replaced by $\|X\|, \|G\|$, respectively.*” The model is the paper's (2.1) (p. 8, $d \ge 2$), with each summand taking finitely many equally likely values. $G$ is the paper's Gaussian model (p. 8: jointly Gaussian entries, $\mathbf E[G] = \mathbf E[X]$, $\mathrm{Cov}(G) = \mathrm{Cov}(X)$), written as in its Remark 2.3 as $Z_0 + \sum_k A_k g_k$ with the particular choice $A_{(i,\omega)} = |\Omega|^{-1/2}Z_i(\omega)$, which has that mean and covariance because the $Z_i(\omega_i)$ are independent and centred. The statement keeps the second and third bounds for the norm. The first bound, which compares $X$ and $G$ on a common probability space, and the $\lambda_{\max}$ forms are not included.
-- source:
--   Brailovskaya, T. and van Handel, R., Universality and sharp matrix concentration inequalities, Geom. Funct. Anal. 34 (2024) 1734–1838, https://doi.org/10.1007/s00039-024-00692-9 (arXiv:2201.05142, whose page numbers are used), p. 12, Corollary 2.7, norm form (finitely many equally likely values), with the Gaussian model of §2.1.2 (p. 8) and the parameters of §2.1.4 (p. 10)

import Mathlib

open Matrix ComplexConjugate MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace BrailovskayaVanHandel

theorem prob_abs_norm_sub_gaussian_gt_le_and_abs_expect_norm_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (D n : ℕ) (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (Z₀ : Matrix (Fin D) (Fin D) ℂ) (Z : Fin n → Ω → Matrix (Fin D) (Fin D) ℂ), 2 ≤ D →
      Z₀.IsHermitian → (∀ i ω, (Z i ω).IsHermitian) → (∀ i, ∑ ω, Z i ω = 0) →
      let card : ℝ := Fintype.card (Fin n → Ω)
      let X : (Fin n → Ω) → Matrix (Fin D) (Fin D) ℂ := fun ω => Z₀ + ∑ i, Z i (ω i)
      let EX : Matrix (Fin D) (Fin D) ℂ := (card : ℂ)⁻¹ • ∑ ω, X ω
      let σ : ℝ := Real.sqrt
        ‖toEuclideanCLM (𝕜 := ℂ) ((card : ℂ)⁻¹ • ∑ ω, (X ω - EX) * (X ω - EX))‖
      let σStar : ℝ := ⨆ (v : EuclideanSpace ℂ (Fin D)) (w : EuclideanSpace ℂ (Fin D))
        (_ : ‖v‖ = 1 ∧ ‖w‖ = 1),
        Real.sqrt ((∑ ω, ‖⟪v, toEuclideanCLM (𝕜 := ℂ) (X ω - EX) w⟫_ℂ‖ ^ 2) / card)
      let R : ℝ := ⨆ (i : Fin n) (ω : Ω), ‖toEuclideanCLM (𝕜 := ℂ) (Z i ω)‖
      let A : Fin n × Ω → Matrix (Fin D) (Fin D) ℂ :=
        fun k => (((Real.sqrt (Fintype.card Ω))⁻¹ : ℝ) : ℂ) • Z k.1 k.2
      let G : (Fin n × Ω → ℝ) → Matrix (Fin D) (Fin D) ℂ := fun g => Z₀ + ∑ k, (g k : ℂ) • A k
      let γ : Measure (Fin n × Ω → ℝ) := Measure.pi fun _ => gaussianReal 0 1
      let EnormG : ℝ := ∫ g, ‖toEuclideanCLM (𝕜 := ℂ) (G g)‖ ∂γ
      (∀ t : ℝ, 0 ≤ t →
        ((Finset.univ.filter fun ω : Fin n → Ω =>
            C * (σStar * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
              R * t) < |‖toEuclideanCLM (𝕜 := ℂ) (X ω)‖ - EnormG|).card : ℝ) / card ≤
          D * Real.exp (-t)) ∧
      |(∑ ω, ‖toEuclideanCLM (𝕜 := ℂ) (X ω)‖) / card - EnormG| ≤
        C * (σStar * Real.sqrt (Real.log D) +
          R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * Real.log D ^ ((2 : ℝ) / 3) + R * Real.log D) := by
  sorry

end BrailovskayaVanHandel
