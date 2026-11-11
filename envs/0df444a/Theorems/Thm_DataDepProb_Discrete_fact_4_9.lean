-- Prove2me | Theorems.Thm_DataDepProb_Discrete_fact_4_9
-- name    : DataDepProb.Discrete.fact_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:11:57.763613+00:00
-- url     : https://prove2.me/theorems/cbbeaac2-f78b-4854-b9d9-4b2ec44b6492
-- title:
--   Fact 4.9 — MW progress in relative entropy: deterministic, fresh-sample and density forms
-- statement:
--   Let $r$ be a positive distribution on $[d]$, $f:[d]\to[0,1]$, $b\in[0,1]$ and $\eta>0$. For every $w\in\Delta_d$,
--   $$\mathrm{KL}(w\|\mathrm{MW}_\eta(r,f,b))\le\mathrm{KL}(w\|r)+\eta(b-E_r[f])(E_r[f]-E_w[f])+\frac{\eta^2(b-E_r[f])^2}8 .$$
--   In particular, if $b=f(Y)$ for an independent $Y\sim D$, $D\in\Delta_d$, then $E_Y\mathrm{KL}(D\|\mathrm{MW}_\eta(r,f,f(Y)))\le\mathrm{KL}(D\|r)-\eta(E_r[f]-E_D[f])^2+\eta^2/8$. The first inequality also holds for probability densities on a common measure space, with integrals in place of sums, whenever $\mathrm{KL}(w\|r)$ is finite and $f$ takes values in $[0,1]$.
--
--   This is the one-step progress of the multiplicative weights method for the squared loss; it drives the potential argument of Lemma 6.1.
--
--   Differences from the source:
--   - encoding: $[d]$ → `Fin d`; "positive distribution $r$" → `r ∈ simplex d` and `∀ x, 0 < r x`; reason: same objects.
--   - reading: $E_Y$ for an independent $Y\sim D$ → $\sum_y D(y)\,(\cdot)$ with $r,f,\eta$ fixed; reason: the expectation over $Y$ alone.
--   - reading: densities on a common measure space with "$r,f,b,\eta$ as above" → measurable $w,r,f$ on an arbitrary measure space $(\alpha,\mu)$, $w\ge0$, $r>0$ everywhere, $\int w\,d\mu=\int r\,d\mu=1$, $f\in[0,1]$, $b\in[0,1]$, $\eta>0$, and the MW update normalized by $\int r e^{\eta(b-E_r f)f}d\mu$; reason: $r$ is positive "as above".
--   - reading: "$\mathrm{KL}(w\|r)$ is finite" → `Integrable (fun x => w x * log (w x / r x)) μ`; reason: the negative part is always integrable, so finiteness is integrability.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 10, Fact 4.9

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_Divergence
import Definitions.Def_DataDepProb_Discrete_MW

open MeasureTheory

namespace DataDepProb.Discrete

/-- Fact 4.9 (MW progress, p. 10). Let `r` be a positive distribution on `[d]`,
`f : [d] → [0, 1]`, `b ∈ [0, 1]`, `η > 0`.
(i) For every `w ∈ ∆_d`, `KL(w‖MW_η(r, f, b)) ≤ KL(w‖r) + η(b − E_r[f])(E_r[f] − E_w[f])
+ η²(b − E_r[f])²/8`.
(ii) If `b = f(Y)` for an independent `Y ∼ D`, `D ∈ ∆_d`, then
`E_Y KL(D‖MW_η(r, f, f(Y))) ≤ KL(D‖r) − η(E_r[f] − E_D[f])² + η²/8`.
(iii) The inequality (i) also holds for probability densities `w, r` (`r > 0`) on a common measure
space, with integrals in place of sums, whenever `KL(w‖r)` is finite and `f` takes values in
`[0, 1]`. -/
theorem fact_4_9 :
    (∀ (d : ℕ) (r f : Fin d → ℝ) (b η : ℝ), r ∈ simplex d → (∀ x, 0 < r x) →
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) → 0 ≤ b → b ≤ 1 → 0 < η →
      (∀ w ∈ simplex d,
        kl w (mw η r f b) ≤ kl w r + η * (b - expect r f) * (expect r f - expect w f)
          + η ^ 2 * (b - expect r f) ^ 2 / 8) ∧
      (∀ D ∈ simplex d,
        ∑ y, D y * kl D (mw η r f (f y)) ≤ kl D r - η * (expect r f - expect D f) ^ 2
          + η ^ 2 / 8)) ∧
    ∀ (α : Type*) [MeasurableSpace α] (μ : Measure α) (w r f : α → ℝ) (b η : ℝ),
      Measurable w → Measurable r → Measurable f →
      (∀ x, 0 ≤ w x) → (∀ x, 0 < r x) → ∫ x, w x ∂μ = 1 → ∫ x, r x ∂μ = 1 →
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) → 0 ≤ b → b ≤ 1 → 0 < η →
      Integrable (fun x => w x * Real.log (w x / r x)) μ →
      klDensity μ w (mwDensity μ η r f b) ≤ klDensity μ w r
        + η * (b - ∫ x, r x * f x ∂μ) * (∫ x, r x * f x ∂μ - ∫ x, w x * f x ∂μ)
        + η ^ 2 * (b - ∫ x, r x * f x ∂μ) ^ 2 / 8 := by sorry

end DataDepProb.Discrete
