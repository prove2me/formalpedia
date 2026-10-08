-- Prove2me | Theorems.Thm_AvgLMS_Expect_lemma_1
-- name    : AvgLMS.Expect.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:05:36.022509+00:00
-- url     : https://prove2.me/theorems/18a6c792-d0da-403a-abe3-784d85738859
-- title:
--   Lemma 1, p. 11 — (1 − γR²)E⟨ᾱₙ₋₁, Hᾱₙ₋₁⟩ + E‖αₙ‖²/(2nγ) ≤ ‖α₀‖²/(2nγ) + (γ/n)Σ E‖ξₖ‖²
-- statement:
--   Let $(\mathcal F_n)$ be an increasing sequence of $\sigma$-fields, and let $(x_n,\xi_n)\in\mathcal H\times\mathcal H$, $n\ge1$, be $\mathcal F_n$-measurable. Assume, for every $n\ge1$:
--   1. $\mathbb E[\xi_n\mid\mathcal F_{n-1}]=0$ and $\mathbb E\|\xi_n\|^2<\infty$;
--   2. $\mathbb E[x_n\otimes x_n\mid\mathcal F_{n-1}]=H$ for a fixed invertible operator $H$;
--   3. $\mathbb E[\|x_n\|^2x_n\otimes x_n\mid\mathcal F_{n-1}]\preccurlyeq R^2H$ for some $R>0$.
--
--   Let $\gamma>0$ with $\gamma R^2\le1$, let $\alpha_0\in\mathcal H$, and let $\alpha_n=(I-\gamma x_n\otimes x_n)\alpha_{n-1}+\gamma\xi_n$ for $n\ge1$, with average $\bar\alpha_{n-1}=n^{-1}\sum_{k=0}^{n-1}\alpha_k$. Then for every $n\ge1$,
--   $$(1-\gamma R^2)\,\mathbb E\langle\bar\alpha_{n-1},H\bar\alpha_{n-1}\rangle+\frac{1}{2n\gamma}\,\mathbb E\|\alpha_n\|^2\le\frac{1}{2n\gamma}\|\alpha_0\|^2+\frac{\gamma}{n}\sum_{k=1}^{n}\mathbb E\|\xi_k\|^2 ,$$
--   and both expectations on the left are finite.
--
--   This is the "weak" bound of the proof, the constant-step analogue of non-strongly-convex SGD results; it applies to any recursion of the LMS type driven by a martingale-difference noise, and is used in the paper for the remainder of the expansion of the noise process.
--
--   **Formalization Note.** Observation $n+1$ is $\mathcal F_{n+1}$-measurable and is conditioned on $\mathcal F_n$. The conditional Loewner conditions are written as quadratic forms: for every $v,w$, $\mathbb E[\langle x_n,v\rangle\langle x_n,w\rangle\mid\mathcal F_{n-1}]=\langle v,Hw\rangle$ and $\mathbb E[\|x_n\|^2\langle x_n,v\rangle^2\mid\mathcal F_{n-1}]\le R^2\langle v,Hv\rangle$ almost surely, each with the integrability of its integrand. The page's "$\mathbb E[\|\xi_n\|^2\mid\mathcal F_{n-1}]$ is finite" is stated as integrability of $\|\xi_n\|^2$; the right-hand side of the conclusion contains $\mathbb E\|\xi_k\|^2$, so the lemma says nothing when it is infinite. $\gamma>0$ and $n\ge1$ are added (a step size; $1/n$). $H^{-1}$ is an explicit two-sided inverse.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, Lemma 1, App. A.1, p. 11

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- Lemma 1, App. A.1, p. 11. Observations are indexed from `1`: `(x (n+1), ξ (n+1))` is
`ℱ (n+1)`-measurable and is conditioned on `ℱ n`. The Loewner conditions are quadratic forms. -/
theorem lemma_1 {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (ℱ : Filtration ℕ m0) (x ξ : ℕ → Ω → Hs d)
    (hx_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (x (n + 1)))
    (hξ_meas : ∀ n, StronglyMeasurable[ℱ (n + 1)] (ξ (n + 1)))
    (hξ_int : ∀ n, Integrable (ξ (n + 1)) μ)
    (hξ_sq : ∀ n, Integrable (fun ω => ‖ξ (n + 1) ω‖ ^ 2) μ)
    (hξ_mean : ∀ n, μ[ξ (n + 1) | ℱ n] =ᵐ[μ] 0)
    (H Hinv : Hs d →L[ℝ] Hs d)
    (hHinv : H.comp Hinv = ContinuousLinearMap.id ℝ (Hs d) ∧
      Hinv.comp H = ContinuousLinearMap.id ℝ (Hs d))
    (hcov_int : ∀ n (v w : Hs d), Integrable (fun ω => ⟪x (n + 1) ω, v⟫_ℝ * ⟪x (n + 1) ω, w⟫_ℝ) μ)
    (hcov : ∀ n (v w : Hs d),
      μ[fun ω => ⟪x (n + 1) ω, v⟫_ℝ * ⟪x (n + 1) ω, w⟫_ℝ | ℱ n] =ᵐ[μ] fun _ => ⟪v, H w⟫_ℝ)
    (R : ℝ) (hR : 0 < R)
    (h4_int : ∀ n (v : Hs d), Integrable (fun ω => ‖x (n + 1) ω‖ ^ 2 * ⟪x (n + 1) ω, v⟫_ℝ ^ 2) μ)
    (h4 : ∀ n (v : Hs d),
      μ[fun ω => ‖x (n + 1) ω‖ ^ 2 * ⟪x (n + 1) ω, v⟫_ℝ ^ 2 | ℱ n] ≤ᵐ[μ] fun _ => R ^ 2 * ⟪v, H v⟫_ℝ)
    (γ : ℝ) (hγ : 0 < γ) (hγR : γ * R ^ 2 ≤ 1)
    (α0 : Hs d) (α : ℕ → Ω → Hs d) (hα0 : α 0 = fun _ => α0)
    (hα : ∀ n ω, α (n + 1) ω =
      α n ω - γ • (⟪x (n + 1) ω, α n ω⟫_ℝ • x (n + 1) ω) + γ • ξ (n + 1) ω)
    (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω => ⟪avg α (n - 1) ω, H (avg α (n - 1) ω)⟫_ℝ) μ ∧
    Integrable (fun ω => ‖α n ω‖ ^ 2) μ ∧
    (1 - γ * R ^ 2) * ∫ ω, ⟪avg α (n - 1) ω, H (avg α (n - 1) ω)⟫_ℝ ∂μ +
        1 / (2 * n * γ) * ∫ ω, ‖α n ω‖ ^ 2 ∂μ ≤
      1 / (2 * n * γ) * ‖α0‖ ^ 2 + γ / n * ∑ k ∈ Finset.Icc 1 n, ∫ ω, ‖ξ k ω‖ ^ 2 ∂μ := by sorry
end AvgLMS.Expect
