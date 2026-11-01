-- Prove2me | Theorems.Thm_DRBatchBandit_theorem_A7
-- name    : DRBatchBandit.theorem_A7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:23:56.833381+00:00
-- url     : https://prove2.me/theorems/0281deb2-8961-4d98-9252-9d7a7b3f6d14
-- title:
--   Theorem A7 (Wainwright, Theorem 4.10), p.42 — $\sup_{f\in\mathcal F}|\mathbf P_nf-\mathbf Pf|\le2\mathcal R_n(\mathcal F)+\epsilon$ with probability $\ge1-e^{-n\epsilon^2/(2B^2)}$
-- statement:
--   Let $z_1,\dots,z_n$ ($n\ge1$) be iid from a probability measure $\mu$ on $Z$, let $B>0$ and $\epsilon\ge0$, and let $\mathcal F$ be a class of functions with $f(z)\in[-B,B]$ for all $f\in\mathcal F$ and $z$. Then with probability at least $1-\exp\big(-\frac{n\epsilon^2}{2B^2}\big)$,
--   $$\sup_{f\in\mathcal F}\Big|\frac1n\sum_{i=1}^nf(z_i)-\mathbf Ef(z)\Big|\le2\mathcal R_n(\mathcal F)+\epsilon.$$
--
--   The paper cites this as Theorem 4.10 of Wainwright, *High-Dimensional Statistics*, and applies it to the weighted classes $\mathcal F_\Pi$, $\mathcal F_{\Pi,x}$ and $\mathcal F_{\Pi,\mathbb D}$ with $B=1/\eta$.
--
--   **Formalization Note** The failure event $\{\exists f\in\mathcal F:\ |\cdot|>2\mathcal R_n(\mathcal F)+\epsilon\}$ is bounded in (outer) measure by $e^{-n\epsilon^2/(2B^2)}$. The class consists of measurable functions and is pointwise separable: a countable subclass approximates every member pointwise.
--
--   Differences from the source:
--   - reading: a class ℱ with f(z) ∈ [−B, B] (measurability left implicit) → measurable members and pointwise separability (a countable subclass approximating every member pointwise); reason: the cited theorem's standing measurability convention; without it the supremum in ℛ_n(ℱ) need not be measurable and Lean's integral of it would be 0
--   - encoding: with probability at least 1 − exp(−nϵ²/(2B²)), sup ≤ 2ℛ_n + ϵ → the (outer) measure of {∃ f ∈ ℱ, 2ℛ_n + ϵ < |…|} is ≤ exp(−nϵ²/(2B²)); reason: same event, stated without a real supremum; the outer measure is the strong reading for a possibly non-measurable event
--   - encoding: n, B, ϵ unspecified → 1 ≤ n, 0 < B, 0 ≤ ϵ; reason: the ranges of the cited theorem (n samples, b-uniformly bounded class, δ ≥ 0)
-- source:
--   Si, Zhang, Zhou & Blanchet, Distributionally Robust Batch Contextual Bandits, arXiv:2006.05630v7, Theorem A7, p.42 (citing Wainwright 2019, Theorem 4.10). PDF sha256 ac485985feb75d33b603f06f5a5d93c52077877db7be11de3d71107c7c374b02

import Mathlib
import Definitions.Def_DRBatchBandit_Rademacher

open MeasureTheory Filter Topology

namespace DRBatchBandit

/-- Theorem A7 (Si, Zhang, Zhou & Blanchet, arXiv:2006.05630v7, p.42; Theorem 4.10 in
Wainwright, *High-Dimensional Statistics*, cited): if every `f ∈ ℱ` takes values in `[−B, B]`,
then with probability at least `1 − exp(−nϵ²/(2B²))`,
`sup_{f ∈ ℱ} |(1/n) ∑ᵢ f(zᵢ) − E f(z)| ≤ 2ℛ_n(ℱ) + ϵ`.

**Formalization Note.** `z₁, …, z_n` are iid from a probability measure `μ`, `n ≥ 1`, `B > 0`,
`ϵ ≥ 0`. The failure event is bounded in (outer) measure. The class consists of measurable
functions and is pointwise separable (a countable subclass approximates every member pointwise),
the standing measurability convention of the cited theorem; it makes the supremum in
`ℛ_n(ℱ)` measurable. -/
theorem theorem_A7 {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (B ϵ : ℝ) (hB : 0 < B) (hϵ : 0 ≤ ϵ) (F : Set (Z → ℝ))
    (hmeas : ∀ f ∈ F, Measurable f) (hbdd : ∀ f ∈ F, ∀ z, |f z| ≤ B)
    (hsep : ∃ F₀ : Set (Z → ℝ), F₀.Countable ∧ F₀ ⊆ F ∧
      ∀ f ∈ F, ∃ u : ℕ → Z → ℝ, (∀ k, u k ∈ F₀) ∧ ∀ z, Tendsto (fun k => u k z) atTop (𝓝 (f z))) :
    (Measure.pi fun _ : Fin n => μ)
        {z | ∃ f ∈ F, 2 * rademacher μ n F + ϵ < |(1 / n : ℝ) * ∑ i, f (z i) - ∫ y, f y ∂μ|}
      ≤ ENNReal.ofReal (Real.exp (-(n * ϵ ^ 2) / (2 * B ^ 2))) := by sorry

end DRBatchBandit
