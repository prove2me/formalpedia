-- Prove2me | Theorems.Thm_DRSub4633_lemma_A_1
-- name    : DRSub4633.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:04:18.170445+00:00
-- url     : https://prove2.me/theorems/429401b9-aea8-4d05-b9e1-6a32f355f226
-- title:
--   Lemma A.1 — reduction of ordered scalar profiles
-- statement:
--   Let $0\le\tau<T\le 1$ and let $q:[\tau,T]\to[1/2,1]$ be nonincreasing. Write
--   $$U_{\tau,T}=\int_\tau^TW(t)\,dt,\qquad L_{\tau,T}=\int_\tau^T\lambda(t)\,dt,\qquad \bar q=\frac1{U_{\tau,T}}\int_\tau^TW(t)q(t)\,dt.$$
--   Then
--   $$\int_\tau^T\{\Lambda(q(t))W(t)+\mathfrak c(q(t))\lambda(t)-\Gamma\}\,dt\le\mathfrak c(\bar q)\{L_{\tau,T}+(b+1-\bar q)U_{\tau,T}\}-\Gamma(T-\tau).\tag{117}$$
--   It reduces the scalar averaging inequality to constant profiles.
--
--   Differences from the source:
--   - encoding: q : [τ, T] → [1/2, 1] nonincreasing → q : ℝ → ℝ, AntitoneOn q [τ, T], values in [1/2, 1] on [τ, T]; reason: values outside [τ, T] are never used; same instances
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma A.1, p.42

import Mathlib
import Definitions.Def_DRSub4633_LamFun
import Definitions.Def_DRSub4633_cFun
import Definitions.Def_DRSub4633_WTail
import Definitions.Def_DRSub4633_lam
import Definitions.Def_DRSub4633_Gam

namespace DRSub4633

/-- **Lemma A.1 (Reduction of ordered scalar profiles).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma A.1, p.42: "Let
`0 ≤ τ < T ≤ 1`, and let `q : [τ, T] → [1/2, 1]` be nonincreasing. Write `U_(τ,T) = ∫_τ^T W(t) dt`,
`L_(τ,T) = ∫_τ^T λ(t) dt`, `q̄ = (1/U_(τ,T)) ∫_τ^T W(t)q(t) dt`. Then
`∫_τ^T {Λ(q(t))W(t) + 𝔠(q(t))λ(t) − Γ} dt ≤ 𝔠(q̄){L_(τ,T) + (b + 1 − q̄)U_(τ,T)} − Γ(T − τ)`. (117)"

**Formalization Note.** `q : ℝ → ℝ` is nonincreasing on `[τ, T]` with values in `[1/2, 1]` there;
its values elsewhere are not used. No measurability is assumed (the page assumes none; a monotone
function is measurable). The closing sentence of the lemma ("Consequently it suffices …") is
commentary and is not formalized. -/
theorem lemma_A_1 (τ T : ℝ) (hτ : 0 ≤ τ) (hτT : τ < T) (hT : T ≤ 1) (q : ℝ → ℝ)
    (hq : AntitoneOn q (Set.Icc τ T)) (hq01 : ∀ t ∈ Set.Icc τ T, q t ∈ Set.Icc (1 / 2 : ℝ) 1) :
    let U : ℝ := ∫ t in τ..T, WTail t
    let L : ℝ := ∫ t in τ..T, lam t
    let qbar : ℝ := (1 / U) * ∫ t in τ..T, WTail t * q t
    ∫ t in τ..T, (LamFun (q t) * WTail t + cFun (q t) * lam t - Gam) ≤
      cFun qbar * (L + (bPar + 1 - qbar) * U) - Gam * (T - τ) := by sorry

end DRSub4633
