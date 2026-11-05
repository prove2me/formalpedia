-- Prove2me | Theorems.Thm_BandeiraBoedihardjoVanHandel_prob_norm_gaussian_gt_le_and_integral_norm_le
-- name    : BandeiraBoedihardjoVanHandel.prob_norm_gaussian_gt_le_and_integral_norm_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-05T01:22:37.775913+00:00
-- url     : https://prove2.me/theorems/cb404198-ae41-4719-8873-f6478ae79c67
-- title:
--   Bandeira–Boedihardjo–van Handel, Corollary 2.2 with Lemma 2.5 — sharp norm bound for Gaussian random matrices
-- statement:
--   There is a universal constant $C > 0$ with the following property. Let $D \ge 2$, let $\iota$ be a finite index set, let $A_0$ and $A_i$ ($i \in \iota$) be arbitrary complex $D \times D$ matrices, and let $X = A_0 + \sum_i g_i A_i$, where the $g_i$ are i.i.d. real standard Gaussians. Put
--   $$s_1 = \Big\|\sum_i A_i^*A_i\Big\|^{1/2},\quad s_2 = \Big\|\sum_i A_iA_i^*\Big\|^{1/2},\quad \sigma = \max(s_1, s_2),\quad \sigma_* = \sup_{\|v\| = \|w\| = 1}\Big(\sum_i |\langle v, A_iw\rangle|^2\Big)^{1/2},$$
--   and $v = \|\mathrm{Cov}\|^{1/2}$, where $\mathrm{Cov}$ is the $D^2 \times D^2$ matrix with entries $\mathrm{Cov}_{(j,k),(l,m)} = \sum_i (A_i)_{jk}\overline{(A_i)_{lm}}$. Let $b = \|A_0\| + s_1 + s_2 + C v^{1/2}\sigma^{1/2}(\log D)^{3/4}$. Then
--   $$\mathbf P\big[\|X\| > b + C\sigma_* t\big] \le e^{-t^2}\quad (t \ge 0),\qquad \mathbf E\|X\| \le b.$$
--   Here $\|\cdot\|$ is the operator norm on $\ell^2$, and the probability and expectation are taken against the standard Gaussian product measure on $\mathbb R^\iota$.
--
--   This is Corollary 2.2 of A. S. Bandeira, M. T. Boedihardjo and R. van Handel, *Matrix concentration inequalities and free probability*, Invent. Math. 234 (2023) 419–487, [doi:10.1007/s00222-023-01204-6](https://doi.org/10.1007/s00222-023-01204-6) (arXiv:2108.06312v2, p. 10), with its noncommutative model bounded by Pisier's estimate, their Lemma 2.5 (p. 11). Corollary 2.2: “*For the model (2.1) with $A_0, \dots, A_n \in \mathrm M_d(\mathbb C)$, we have $\mathbf P\big[\|X\| > \|X_{\rm free}\| + C\tilde v(X)(\log d)^{\frac34} + C\sigma_*(X)t\big] \le e^{-t^2}$ for all $t \ge 0$, where $C$ is a universal constant. Moreover, $\mathbf E\|X\| \le \|X_{\rm free}\| + C\tilde v(X)(\log d)^{\frac34}$.*” Lemma 2.5 (Pisier): “*For the model (2.1) with $A_0, \dots, A_n \in \mathrm M_d(\mathbb C)$, we have $\|A_0\| \vee \sigma(X) \le \|X_{\rm free}\| \le \|A_0\| + \big\|\sum_{i=1}^n A_i^*A_i\big\|^{\frac12} + \big\|\sum_{i=1}^n A_iA_i^*\big\|^{\frac12}$.*” The paper notes that “the combination of Corollary 2.2 and Lemma 2.5 immediately yields a Gaussian matrix concentration inequality of the form (1.5)”; this statement is that combination, so it makes no reference to the free model $X_{\rm free}$. The model (2.1) (p. 9) fixes $d \ge 2$. The parameters are those of p. 10, with $\tilde v(X) = (v(X)\sigma(X))^{1/2}$. The paper writes $v(X)^2 = \sup_{\mathrm{Tr}|M|^2 \le 1}\sum_i|\mathrm{Tr}[A_iM]|^2$. That is the norm of the matrix $\sum_i \bar a_i a_i^{\mathsf T}$ for $a_i$ the entry vector of $A_i$, which is the entrywise conjugate of $\mathrm{Cov}$ above and so has the same norm.
-- source:
--   Bandeira, A. S., Boedihardjo, M. T. and van Handel, R., Matrix concentration inequalities and free probability, Invent. Math. 234 (2023) 419–487, https://doi.org/10.1007/s00222-023-01204-6 (arXiv:2108.06312v2, whose page numbers are used), pp. 10–11, Corollary 2.2 combined with Lemma 2.5 (Pisier), model (2.1) on p. 9

import Mathlib

open Matrix ComplexConjugate MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace BandeiraBoedihardjoVanHandel

theorem prob_norm_gaussian_gt_le_and_integral_norm_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ) (ι : Type) [Fintype ι]
      (A₀ : Matrix (Fin D) (Fin D) ℂ) (A : ι → Matrix (Fin D) (Fin D) ℂ), 2 ≤ D →
      let X : (ι → ℝ) → Matrix (Fin D) (Fin D) ℂ := fun g => A₀ + ∑ i, (g i : ℂ) • A i
      let γ : Measure (ι → ℝ) := Measure.pi fun _ => gaussianReal 0 1
      let s₁ : ℝ := Real.sqrt ‖toEuclideanCLM (𝕜 := ℂ) (∑ i, (A i)ᴴ * A i)‖
      let s₂ : ℝ := Real.sqrt ‖toEuclideanCLM (𝕜 := ℂ) (∑ i, A i * (A i)ᴴ)‖
      let σ : ℝ := max s₁ s₂
      let σStar : ℝ := ⨆ (v : EuclideanSpace ℂ (Fin D)) (w : EuclideanSpace ℂ (Fin D))
        (_ : ‖v‖ = 1 ∧ ‖w‖ = 1),
        Real.sqrt (∑ i, ‖⟪v, toEuclideanCLM (𝕜 := ℂ) (A i) w⟫_ℂ‖ ^ 2)
      let Cov : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
        fun p q => ∑ i, A i p.1 p.2 * conj (A i q.1 q.2)
      let v : ℝ := Real.sqrt ‖toEuclideanCLM (𝕜 := ℂ) Cov‖
      let bound : ℝ := ‖toEuclideanCLM (𝕜 := ℂ) A₀‖ + s₁ + s₂ +
        C * Real.sqrt v * Real.sqrt σ * Real.log D ^ ((3 : ℝ) / 4)
      (∀ t : ℝ, 0 ≤ t →
        γ {g | bound + C * σStar * t < ‖toEuclideanCLM (𝕜 := ℂ) (X g)‖} ≤
          ENNReal.ofReal (Real.exp (-t ^ 2))) ∧
      ∫ g, ‖toEuclideanCLM (𝕜 := ℂ) (X g)‖ ∂γ ≤ bound := by
  sorry

end BandeiraBoedihardjoVanHandel
