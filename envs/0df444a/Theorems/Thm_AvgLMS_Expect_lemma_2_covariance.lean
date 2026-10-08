-- Prove2me | Theorems.Thm_AvgLMS_Expect_lemma_2_covariance
-- name    : AvgLMS.Expect.lemma_2_covariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:05:44.690085+00:00
-- url     : https://prove2.me/theorems/b6ce8c8a-dd3d-4cae-928b-8a3b67370ef2
-- title:
--   Lemma 2, Eq. (13), p. 12 — E[αₙ ⊗ αₙ] ≼ (I − γH)ⁿα₀ ⊗ α₀(I − γH)ⁿ + γ²Σ(I − γH)ⁿ⁻ᵏC(I − γH)ⁿ⁻ᵏ
-- statement:
--   Let $(\mathcal F_n)$ be an increasing sequence of $\sigma$-fields and $\xi_n\in\mathcal H$, $n\ge1$, be $\mathcal F_n$-measurable with $\mathbb E[\xi_n\mid\mathcal F_{n-1}]=0$, $\mathbb E\|\xi_n\|^2<\infty$ and $\mathbb E[\xi_n\otimes\xi_n]\preccurlyeq C$ for all $n\ge1$. Let $H$ be an invertible positive self-adjoint operator and $\gamma>0$ with $\gamma H\preccurlyeq I$, and let $\alpha_n=(I-\gamma H)\alpha_{n-1}+\gamma\xi_n$ for $n\ge1$, started at a deterministic $\alpha_0$. Then for every $n\ge0$,
--   $$\mathbb E[\alpha_n\otimes\alpha_n]\preccurlyeq(I-\gamma H)^n\alpha_0\otimes\alpha_0(I-\gamma H)^n+\gamma^2\sum_{k=1}^{n}(I-\gamma H)^{n-k}C(I-\gamma H)^{n-k}.$$
--
--   The recursion is the LMS recursion with $x_n\otimes x_n$ replaced by its mean $H$; the bound is the second-moment expansion of its closed form, in which martingale-difference noise contributes additively.
--
--   **Formalization Note.** The page prints "$=$" in (13). With the hypothesis $\mathbb E[\xi_n\otimes\xi_n]\preccurlyeq C$ equality is false in general (for $\xi\equiv0$ and $C=I$ the left side has no $\gamma^2$ term), and the proof uses (13) only as "$\preccurlyeq$" (in (17)), so the order is stated. Both orders are written as quadratic forms: for every $v$, $\mathbb E\langle\alpha_n,v\rangle^2\le\langle(I-\gamma H)^nv,\alpha_0\rangle^2+\gamma^2\sum_{k=1}^n\langle(I-\gamma H)^{n-k}v,C(I-\gamma H)^{n-k}v\rangle$, with integrability of the left integrand. The positivity and self-adjointness of $H$ are added: "$\gamma H\preccurlyeq I$" is an order between self-adjoint operators, and in every use in the paper $H$ is a covariance operator. $\gamma>0$ is added.
-- source:
--   Bach & Moulines, arXiv:1306.2119v1, Lemma 2, Eq. (13), App. A.1, p. 12

import Mathlib
import Definitions.Def_AvgLMS_Expect_Model

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace RealInnerProductSpace

namespace AvgLMS.Expect

/-- Lemma 2, Eq. (13), App. A.1, p. 12, with `≼` in place of the printed `=` and written as
quadratic forms: for every `v`,
`E⟨αₙ, v⟩² ≤ ⟨(I − γH)ⁿ v, α₀⟩² + γ² ∑_{k=1}^{n} ⟨(I − γH)ⁿ⁻ᵏ v, C (I − γH)ⁿ⁻ᵏ v⟩`
(here `n − k ≥ 0` since `k ≤ n`). `E[ξₙ ⊗ ξₙ] ≼ C` is `∀ v, E⟨ξₙ, v⟩² ≤ ⟨v, Cv⟩`; `H` is
self-adjoint and positive (added, see the Formalization Note). -/
theorem lemma_2_covariance {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
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
    (hα : ∀ n ω, α (n + 1) ω = (1 - γ • H) (α n ω) + γ • ξ (n + 1) ω) :
    ∀ (n : ℕ) (v : Hs d), Integrable (fun ω => ⟪α n ω, v⟫_ℝ ^ 2) μ ∧
      ∫ ω, ⟪α n ω, v⟫_ℝ ^ 2 ∂μ ≤
        ⟪((1 - γ • H) ^ n) v, α0⟫_ℝ ^ 2 +
          γ ^ 2 * ∑ k ∈ Finset.Icc 1 n,
            ⟪((1 - γ • H) ^ (n - k)) v, C (((1 - γ • H) ^ (n - k)) v)⟫_ℝ := by sorry
end AvgLMS.Expect
