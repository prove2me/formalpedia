-- Prove2me | Theorems.Thm_ForkJoinDelay_eq_4_coefficients
-- name    : ForkJoinDelay.eq_4_coefficients
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:30:49.901316+00:00
-- url     : https://prove2.me/theorems/1c8560e0-7866-47ef-bd18-043299021380
-- title:
--   Eq. (4) — closed form of $a$ and integral forms of $b,c,d$
-- statement:
--   Let $\mu_0,\mu_1,\mu_2>0$, $w_0\in\mathbb C$ with $\operatorname{Re}w_0\ge0$, and $\lambda=\mu_0+w_0+\mu_1+\mu_2$. For all $r_1,r_2,h_1,h_2\ge0$:
--
--   1. the defining integral of $a$ (p.10) has the closed form
--   $$\int_0^\infty e^{-(w_0+\mu_1+\mu_2)t}\frac{(\mu_1t)^{r_1}}{r_1!}\frac{(\mu_2t)^{r_2}}{r_2!}\mu_0e^{-\mu_0t}\,dt=\binom{r_1+r_2}{r_1}\frac{\mu_0}{\lambda}\Bigl(\frac{\mu_1}{\lambda}\Bigr)^{r_1}\Bigl(\frac{\mu_2}{\lambda}\Bigr)^{r_2}=a(r_1,r_2);$$
--   2. $a(r_1,r_2)=\dfrac{\mu_0}{\mu_0+w_0}\displaystyle\int_0^\infty(\mu_0+w_0)e^{-(\mu_0+w_0)t}e^{-\mu_1t}\frac{(\mu_1t)^{r_1}}{r_1!}e^{-\mu_2t}\frac{(\mu_2t)^{r_2}}{r_2!}\,dt$;
--   3. $b(r_1,h_2)=\displaystyle\sum_{r_2=h_2}^\infty a(r_1,r_2)=\int_0^\infty e^{-(w_0+\mu_1+\mu_2)t}\sum_{r_2=h_2}^\infty\frac{(\mu_1t)^{r_1}}{r_1!}\frac{(\mu_2t)^{r_2}}{r_2!}\mu_0e^{-\mu_0t}\,dt$;
--   4. $b(r_1,h_2)=\dfrac{\mu_0}{\mu_0+w_0}\displaystyle\int_0^\infty(\mu_0+w_0)e^{-(\mu_0+w_0)t}e^{-\mu_1t}\frac{(\mu_1t)^{r_1}}{r_1!}\Bigl(1-\sum_{r_2=0}^{h_2-1}e^{-\mu_2t}\frac{(\mu_2t)^{r_2}}{r_2!}\Bigr)dt$;
--   5. $c(h_1,r_2)=\dfrac{\mu_0}{\mu_0+w_0}\displaystyle\int_0^\infty(\mu_0+w_0)e^{-(\mu_0+w_0)t}e^{-\mu_2t}\frac{(\mu_2t)^{r_2}}{r_2!}\Bigl(1-\sum_{r_1=0}^{h_1-1}e^{-\mu_1t}\frac{(\mu_1t)^{r_1}}{r_1!}\Bigr)dt$;
--   6. $d(h_1,h_2)=\dfrac{\mu_0}{\mu_0+w_0}\displaystyle\int_0^\infty(\mu_0+w_0)e^{-(\mu_0+w_0)t}\Bigl(1-\sum_{r_1=0}^{h_1-1}e^{-\mu_1t}\frac{(\mu_1t)^{r_1}}{r_1!}\Bigr)\Bigl(1-\sum_{r_2=0}^{h_2-1}e^{-\mu_2t}\frac{(\mu_2t)^{r_2}}{r_2!}\Bigr)dt$.
--
--   Here $b,c,d$ are the tail sums of $a$ defined on pp.10–11. The closed form makes the recursion (3) computable without numerical integration.
--
--   Differences from the source:
--   - reading: service 'rates' µ0, µ1, µ2 → 0 < µ0, µ1, µ2; reason: a rate of an exponential law is positive
--   - generalization: transform argument w0 (domain not stated; LST on real w0 ≥ 0) → complex w0 with Re w0 ≥ 0; reason: real w0 ≥ 0 is the special case; the paper evaluates the transform at imaginary arguments (Fourier inversion, p.13); every formula is defined there
--   - encoding: infinite sums Σ_{r=h}^∞ → tsum over n with r = h + n; reason: the families are absolutely summable, so the tsum is the true sum
--   - encoding: ∫_0^∞ … dt → Bochner integral over Set.Ioi 0; reason: the integrands are integrable on (0, ∞); same value
--   - encoding: a(r1,r2) defined as an integral (p.10) → a(r1,r2) in the closed form of (4) (coefA); b, c, d the tsums of it; reason: the first clause of this item states that the two agree
--   - encoding: Σ_{r=0}^{h−1} at h = 0 in (4) → empty Finset.range sum, equal to 0; reason: the empty-sum convention of p.11
-- source:
--   Carmeli, Yom-Tov, Boxma, State-Dependent Estimation of Delay Distributions in Fork-Join Networks, author manuscript (sha256 c8b2002d…9d1c), §3, pp.10–11 (definitions of a, b, c, d) and Eq. (4), p.11

import Mathlib
import Definitions.Def_ForkJoinDelay_coefA
import Definitions.Def_ForkJoinDelay_coefB
import Definitions.Def_ForkJoinDelay_coefC
import Definitions.Def_ForkJoinDelay_coefD

open MeasureTheory

namespace ForkJoinDelay

/-- **The coefficients `a, b, c, d`: Eq. (4) and the definitions of pp.10–11.**
Carmeli, Yom-Tov, Boxma, *State-Dependent Estimation of Delay Distributions in Fork-Join
Networks*, author manuscript, §3, pp.10–11, and Eq. (4), p.11. For positive rates and complex
`w₀` with `Re w₀ ≥ 0`, and all `r₁, r₂, h₁, h₂ ≥ 0`:

1. (definition of `a`, p.10) `∫₀^∞ e^{−(w₀+µ₁+µ₂)t} (µ₁t)^{r₁}/r₁! (µ₂t)^{r₂}/r₂! µ₀e^{−µ₀t} dt`
   equals the closed form `a(r₁,r₂) = C(r₁+r₂,r₁) µ₀/λ (µ₁/λ)^{r₁} (µ₂/λ)^{r₂}`,
   `λ = µ₀+w₀+µ₁+µ₂` (`coefA`);
2. (first line of (4)) `µ₀/(µ₀+w₀) ∫₀^∞ (µ₀+w₀)e^{−(µ₀+w₀)t} e^{−µ₁t}(µ₁t)^{r₁}/r₁! e^{−µ₂t}(µ₂t)^{r₂}/r₂! dt`
   equals the same closed form;
3. (definition of `b`, p.10) `b(r₁,h₂) = Σ_{r₂≥h₂} a(r₁,r₂)` equals
   `∫₀^∞ e^{−(w₀+µ₁+µ₂)t} Σ_{r₂≥h₂} (µ₁t)^{r₁}/r₁! (µ₂t)^{r₂}/r₂! µ₀e^{−µ₀t} dt`;
4. (4) `b(r₁,h₂) = µ₀/(µ₀+w₀) ∫₀^∞ (µ₀+w₀)e^{−(µ₀+w₀)t} e^{−µ₁t}(µ₁t)^{r₁}/r₁! (1 − Σ_{r₂<h₂} e^{−µ₂t}(µ₂t)^{r₂}/r₂!) dt`;
5. (4) `c(h₁,r₂) = µ₀/(µ₀+w₀) ∫₀^∞ (µ₀+w₀)e^{−(µ₀+w₀)t} e^{−µ₂t}(µ₂t)^{r₂}/r₂! (1 − Σ_{r₁<h₁} e^{−µ₁t}(µ₁t)^{r₁}/r₁!) dt`;
6. (4) `d(h₁,h₂) = µ₀/(µ₀+w₀) ∫₀^∞ (µ₀+w₀)e^{−(µ₀+w₀)t} (1 − Σ_{r₁<h₁} …)(1 − Σ_{r₂<h₂} …) dt`.

**Formalization Note.** `b, c, d` are the `tsum`s `coefB`, `coefC`, `coefD` of the closed form
`coefA`; the integrals are Bochner integrals over `Set.Ioi 0`, with the printed integrands (the
factor `µ₀ + w₀` is not cancelled; it is nonzero since `Re (µ₀ + w₀) > 0`). -/
theorem eq_4_coefficients (μ₀ μ₁ μ₂ : ℝ) (hμ₀ : 0 < μ₀) (hμ₁ : 0 < μ₁) (hμ₂ : 0 < μ₂)
    (w₀ : ℂ) (hw₀ : 0 ≤ w₀.re) (r₁ r₂ h₁ h₂ : ℕ) :
    (∫ t in Set.Ioi (0 : ℝ), Complex.exp (-((w₀ + μ₁ + μ₂) * t)) *
        (((μ₁ * t) ^ r₁ / (r₁.factorial : ℝ) * ((μ₂ * t) ^ r₂ / (r₂.factorial : ℝ)) : ℝ) : ℂ) *
        ((μ₀ * Real.exp (-(μ₀ * t)) : ℝ) : ℂ)) = coefA μ₀ μ₁ μ₂ w₀ r₁ r₂ ∧
    (μ₀ : ℂ) / (μ₀ + w₀) *
        (∫ t in Set.Ioi (0 : ℝ), (μ₀ + w₀) * Complex.exp (-((μ₀ + w₀) * t)) *
          ((Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ r₁ / (r₁.factorial : ℝ) *
            (Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ r₂ / (r₂.factorial : ℝ)) : ℝ) : ℂ)) =
      coefA μ₀ μ₁ μ₂ w₀ r₁ r₂ ∧
    coefB μ₀ μ₁ μ₂ w₀ r₁ h₂ =
      (∫ t in Set.Ioi (0 : ℝ), Complex.exp (-((w₀ + μ₁ + μ₂) * t)) *
        (∑' n : ℕ, (((μ₁ * t) ^ r₁ / (r₁.factorial : ℝ) *
          ((μ₂ * t) ^ (h₂ + n) / ((h₂ + n).factorial : ℝ)) : ℝ) : ℂ)) *
        ((μ₀ * Real.exp (-(μ₀ * t)) : ℝ) : ℂ)) ∧
    coefB μ₀ μ₁ μ₂ w₀ r₁ h₂ =
      (μ₀ : ℂ) / (μ₀ + w₀) *
        (∫ t in Set.Ioi (0 : ℝ), (μ₀ + w₀) * Complex.exp (-((μ₀ + w₀) * t)) *
          ((Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ r₁ / (r₁.factorial : ℝ) *
            (1 - ∑ r ∈ Finset.range h₂,
              Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ r / (r.factorial : ℝ)) : ℝ) : ℂ)) ∧
    coefC μ₀ μ₁ μ₂ w₀ h₁ r₂ =
      (μ₀ : ℂ) / (μ₀ + w₀) *
        (∫ t in Set.Ioi (0 : ℝ), (μ₀ + w₀) * Complex.exp (-((μ₀ + w₀) * t)) *
          ((Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ r₂ / (r₂.factorial : ℝ) *
            (1 - ∑ r ∈ Finset.range h₁,
              Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ r / (r.factorial : ℝ)) : ℝ) : ℂ)) ∧
    coefD μ₀ μ₁ μ₂ w₀ h₁ h₂ =
      (μ₀ : ℂ) / (μ₀ + w₀) *
        (∫ t in Set.Ioi (0 : ℝ), (μ₀ + w₀) * Complex.exp (-((μ₀ + w₀) * t)) *
          (((1 - ∑ r ∈ Finset.range h₁,
              Real.exp (-(μ₁ * t)) * (μ₁ * t) ^ r / (r.factorial : ℝ)) *
            (1 - ∑ r ∈ Finset.range h₂,
              Real.exp (-(μ₂ * t)) * (μ₂ * t) ^ r / (r.factorial : ℝ)) : ℝ) : ℂ)) := by sorry

end ForkJoinDelay
