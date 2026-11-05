-- Prove2me | Theorems.Thm_BrailovskayaVanHandel_prob_norm_sum_gt_le
-- name    : BrailovskayaVanHandel.prob_norm_sum_gt_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T00:30:34.569884+00:00
-- url     : https://prove2.me/theorems/4bde1db6-8d98-4fb4-b098-9dfcd1aacbe3
-- title:
--   Brailovskaya–van Handel, Corollary 2.17 — user-friendly sharp matrix concentration (self-adjoint, finite uniform form)
-- statement:
--   There is a universal constant $C > 0$ with the following property. Let $D \ge 2$ and $n \ge 0$, let $\Omega$ be a finite nonempty set, and let $Z_1, \dots, Z_n : \Omega \to M_D(\mathbb C)$ take Hermitian values with $\sum_{\omega \in \Omega} Z_i(\omega) = 0$ for each $i$. Draw $\omega = (\omega_1, \dots, \omega_n)$ uniformly from $\Omega^n$, so that $Z_i(\omega_i)$ are independent, mean-zero, self-adjoint random matrices, and put $Y = \sum_i Z_i(\omega_i)$. Then for every $t \ge 0$,
--   $$\mathbf P\Big[\|Y\| > 2\sigma(Y) + C\big(v(Y)^{1/2}\sigma(Y)^{1/2}(\log D)^{3/4} + \sigma_*(Y)\,t^{1/2} + R(Y)^{1/3}\sigma(Y)^{2/3}t^{2/3} + R(Y)\,t\big)\Big] \le 4De^{-t}.$$
--   Here $\|\cdot\|$ is the operator norm on $\ell^2$, and the parameters are those of Brailovskaya–van Handel §2.1.4 (p. 10): $\sigma(Y) = \|\mathbf E[(Y - \mathbf EY)^2]\|^{1/2}$; $\sigma_*(Y) = \sup_{\|v\| = \|w\| = 1}\mathbf E\big[|\langle v, (Y - \mathbf EY)w\rangle|^2\big]^{1/2}$; $v(Y) = \|\mathrm{Cov}(Y)\|^{1/2}$, where $\mathrm{Cov}(Y)_{ij,kl} = \mathbf E\big[(Y - \mathbf EY)_{ij}\overline{(Y - \mathbf EY)_{kl}}\big]$ is the $D^2 \times D^2$ covariance matrix of the entries (eq. (2.2), p. 8); and $R(Y) = \max_i \sup_\omega \|Z_i(\omega)\|$. Expectations and the probability are uniform averages over $\Omega^n$.
--
--   This is Corollary 2.17 of T. Brailovskaya and R. van Handel, *Universality and sharp matrix concentration inequalities*, Geom. Funct. Anal. 34 (2024) 1734–1838 (arXiv:2201.05142, p. 15): “*Let $Y = \sum_{i=1}^n Z_i$, where $Z_1, \dots, Z_n$ are independent (possibly non-self-adjoint) $d \times d$ random matrices with $\mathbf E[Z_i] = 0$. Then $\mathbf P\big[\|Y\| \ge \|\mathbf EY^*Y\|^{\frac12} + \|\mathbf EYY^*\|^{\frac12} + C\{v(Y)^{\frac12}\sigma(Y)^{\frac12}(\log d)^{\frac34} + \sigma_*(Y)t^{\frac12} + R(Y)^{\frac13}\sigma(Y)^{\frac23}t^{\frac23} + R(Y)t\}\big] \le 4de^{-t}$ for a universal constant $C$ and all $t \ge 0$*”, in the special case it is applied in its §3.2: self-adjoint summands (so that $\|\mathbf EY^*Y\|^{1/2} + \|\mathbf EYY^*\|^{1/2} = 2\sigma(Y)$), each taking finitely many equally likely values, and $d \ge 2$ as in the paper's model (2.1). The event is stated with the strict inequality $>$, the complement of the spectral containment of the paper's Theorem 2.16, from which the corollary is derived. The paper's Theorem 3.8 (random $2k$-regular graphs on $d$ vertices with $k \gg (\log d)^4$ are nearly Ramanujan) is this bound applied to sums of i.i.d. permutation matrices.
-- source:
--   Brailovskaya, T. and van Handel, R., Universality and sharp matrix concentration inequalities, Geom. Funct. Anal. 34 (2024) 1734–1838, https://doi.org/10.1007/s00039-024-00692-9 (arXiv:2201.05142, whose page numbers are used), p. 15, Corollary 2.17 (self-adjoint case, finitely many equally likely values), with the parameters of §2.1.4 (p. 10)

import Mathlib

open Matrix ComplexConjugate
open scoped InnerProductSpace

namespace BrailovskayaVanHandel

theorem prob_norm_sum_gt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (D n : ℕ) (Ω : Type) [Fintype Ω] [Nonempty Ω]
      (Z : Fin n → Ω → Matrix (Fin D) (Fin D) ℂ), 2 ≤ D →
      (∀ i ω, (Z i ω).IsHermitian) → (∀ i, ∑ ω, Z i ω = 0) → ∀ t : ℝ, 0 ≤ t →
      let card : ℝ := Fintype.card (Fin n → Ω)
      let Y : (Fin n → Ω) → Matrix (Fin D) (Fin D) ℂ := fun ω => ∑ i, Z i (ω i)
      let EY : Matrix (Fin D) (Fin D) ℂ := (card : ℂ)⁻¹ • ∑ ω, Y ω
      let σ : ℝ := Real.sqrt
        ‖toEuclideanCLM (𝕜 := ℂ) ((card : ℂ)⁻¹ • ∑ ω, (Y ω - EY) * (Y ω - EY))‖
      let σStar : ℝ := ⨆ (v : EuclideanSpace ℂ (Fin D)) (w : EuclideanSpace ℂ (Fin D))
        (_ : ‖v‖ = 1 ∧ ‖w‖ = 1),
        Real.sqrt ((∑ ω, ‖⟪v, toEuclideanCLM (𝕜 := ℂ) (Y ω - EY) w⟫_ℂ‖ ^ 2) / card)
      let Cov : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ := fun p q =>
        (card : ℂ)⁻¹ * ∑ ω, (Y ω - EY) p.1 p.2 * conj ((Y ω - EY) q.1 q.2)
      let v : ℝ := Real.sqrt ‖toEuclideanCLM (𝕜 := ℂ) Cov‖
      let R : ℝ := ⨆ (i : Fin n) (ω : Ω), ‖toEuclideanCLM (𝕜 := ℂ) (Z i ω)‖
      ((Finset.univ.filter fun ω : Fin n → Ω =>
          2 * σ + C * (Real.sqrt v * Real.sqrt σ * Real.log D ^ ((3 : ℝ) / 4) +
            σStar * Real.sqrt t + R ^ ((1 : ℝ) / 3) * σ ^ ((2 : ℝ) / 3) * t ^ ((2 : ℝ) / 3) +
            R * t) < ‖toEuclideanCLM (𝕜 := ℂ) (Y ω)‖).card : ℝ) / card ≤
        4 * D * Real.exp (-t) := by
  sorry

end BrailovskayaVanHandel
