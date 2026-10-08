-- Prove2me | Theorems.Thm_AvgLMS_Expect_lemma_2
-- name    : AvgLMS.Expect.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:05:52.234908+00:00
-- url     : https://prove2.me/theorems/1b67dd34-3a61-4791-9811-2cd7a0272e74
-- title:
--   Lemma 2, Eq. (14), p. 12 — E⟨ᾱₙ₋₁, Hᾱₙ₋₁⟩ ≤ ‖α₀‖²/(nγ) + tr(CH⁻¹)/n
-- statement:
--   Under the hypotheses of Lemma 2 — an increasing sequence of $\sigma$-fields $(\mathcal F_n)$, $\mathcal F_n$-measurable $\xi_n\in\mathcal H$ with $\mathbb E[\xi_n\mid\mathcal F_{n-1}]=0$, $\mathbb E\|\xi_n\|^2<\infty$ and $\mathbb E[\xi_n\otimes\xi_n]\preccurlyeq C$; an invertible positive self-adjoint $H$ and $\gamma>0$ with $\gamma H\preccurlyeq I$; and the recursion $\alpha_n=(I-\gamma H)\alpha_{n-1}+\gamma\xi_n$ from a deterministic $\alpha_0$ — the average $\bar\alpha_{n-1}=n^{-1}\sum_{k=0}^{n-1}\alpha_k$ satisfies, for every $n\ge1$,
--   $$\mathbb E\langle\bar\alpha_{n-1},H\bar\alpha_{n-1}\rangle\le\frac{1}{n\gamma}\|\alpha_0\|^2+\frac{\operatorname{tr}(CH^{-1})}{n},$$
--   and the expectation is finite.
--
--   This is the bound that yields the $O(1/n)$ rate: the noise term $\operatorname{tr}(CH^{-1})/n$ does not depend on the smallest eigenvalue of $H$, and with $C=\sigma^2H$ it equals $\sigma^2d/n$.
--
--   **Formalization Note.** $\mathbb E[\xi_n\otimes\xi_n]\preccurlyeq C$ is written as $\mathbb E\langle\xi_n,v\rangle^2\le\langle v,Cv\rangle$ for all $v$, and $\gamma H\preccurlyeq I$ as $\gamma\langle v,Hv\rangle\le\|v\|^2$. $H^{-1}$ is an explicit two-sided inverse and $\operatorname{tr}(CH^{-1})$ is the trace of the composite $C\circ H^{-1}$. The positivity and self-adjointness of $H$, $\gamma>0$ and $n\ge1$ are added (see Eq. (13)).
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, Lemma 2, Eq. (14), App. A.1, p. 12

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- Lemma 2, Eq. (14), App. A.1, p. 12:
`E⟨ᾱₙ₋₁, H ᾱₙ₋₁⟩ ≤ ‖α₀‖²/(nγ) + tr(C H⁻¹)/n`. `E[ξₙ ⊗ ξₙ] ≼ C` is `∀ v, E⟨ξₙ, v⟩² ≤ ⟨v, Cv⟩`;
`H` is self-adjoint and positive (added, see the Formalization Note). -/
theorem lemma_2 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (ℱ : Filtration ℕ m0) (ξ : ℕ → Ω → Hs d)
    (hξ_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (ξ (n + 1)))
    (hξ_int : ∀ n, Integrable (ξ (n + 1)) μ)
    (hξ_sq : ∀ n, Integrable (fun ω => ‖ξ (n + 1) ω‖ ^ 2) μ)
    (hξ_mean : ∀ n, μ[ξ (n + 1) | ℱ n] =ᵐ[μ] 0)
    (C : Hs d →L[ℝ] Hs d) (hC : ∀ n (v : Hs d), ∫ ω, ⟪ξ (n + 1) ω, v⟫_ℝ ^ 2 ∂μ ≤ ⟪v, C v⟫_ℝ)
    (H Hinv : Hs d →L[ℝ] Hs d)
    (hHinv : H.comp Hinv = ContinuousLinearMap.id ℝ (Hs d) ∧
      Hinv.comp H = ContinuousLinearMap.id ℝ (Hs d))
    (hHpos : H.IsPositive)
    (γ : ℝ) (hγ : 0 < γ) (hγH : ∀ v : Hs d, γ * ⟪v, H v⟫_ℝ ≤ ‖v‖ ^ 2)
    (α0 : Hs d) (α : ℕ → Ω → Hs d) (hα0 : α 0 = fun _ => α0)
    (hα : ∀ n ω, α (n + 1) ω = (1 - γ • H) (α n ω) + γ • ξ (n + 1) ω)
    (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω => ⟪avg α (n - 1) ω, H (avg α (n - 1) ω)⟫_ℝ) μ ∧
    ∫ ω, ⟪avg α (n - 1) ω, H (avg α (n - 1) ω)⟫_ℝ ∂μ ≤
      1 / (n * γ) * ‖α0‖ ^ 2 +
        LinearMap.trace ℝ (Hs d) ((C.comp Hinv : Hs d →L[ℝ] Hs d) : Hs d →ₗ[ℝ] Hs d) / n := by sorry
end AvgLMS.Expect
