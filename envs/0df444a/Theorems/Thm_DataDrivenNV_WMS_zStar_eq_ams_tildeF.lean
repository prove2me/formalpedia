-- Prove2me | Theorems.Thm_DataDrivenNV_WMS_zStar_eq_ams_tildeF
-- name    : DataDrivenNV.WMS.zStar_eq_ams_tildeF
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:36:14.242164+00:00
-- url     : https://prove2.me/theorems/889b5dc4-191a-40a4-ba3c-e12365a3e0ea
-- title:
--   Proof of Proposition 2, p. 16 — the AMS of f̃ at q equals z*_{q,γ₀,γ₁} (case γ₁ ≠ 0, open range)
-- statement:
--   Let $b,h,\gamma_0>0$, $q\in\mathbb R$ and $\gamma_1\neq0$ with $-\frac{b+h}{h}<\frac{\gamma_1}{\gamma_0}<\frac{b+h}{b}$, and let $\tilde f$ be the truncated exponential density (12). Then its absolute mean spread at $q$ is
--   $$\Delta_{\tilde f}(q)=\frac{\gamma_0}{\gamma_1^2}\Big[\Big(\frac{b+h}{h}+\frac{\gamma_1}{\gamma_0}\Big)\log\Big(1+\frac{\gamma_1}{\gamma_0}\frac{h}{b+h}\Big)+\Big(\frac{b+h}{b}-\frac{\gamma_1}{\gamma_0}\Big)\log\Big(1-\frac{\gamma_1}{\gamma_0}\frac{b}{b+h}\Big)\Big]=z^*_{q,\gamma_0,\gamma_1}.$$
--
--   With Proposition 1 this is the optimal value of problem (11) in the interior case; Lemma 4 then bounds it below by $\frac1{\gamma_0}\frac{\min(b,h)}{b+h}$.
--
--   **Formalization Note** The paper states this formula as the first of three cases in the proof of Proposition 2; the boundary cases $\gamma_1/\gamma_0=(b+h)/b$ and $\gamma_1/\gamma_0=-(b+h)/h$ (and $\gamma_1=0$) are not part of this statement.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 16, proof of Proposition 2, first case

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

namespace DataDrivenNV.WMS

open MeasureTheory

/-- **Optimal value of (11)** (proof of Proposition 2, p. 16), case
`γ₁/γ₀ ∈ (−(b+h)/h, (b+h)/b)`, `γ₁ ≠ 0`: the AMS at `q` of the extremal density (12) equals
`z* = (γ₀/γ₁²)[((b+h)/h + γ₁/γ₀) log(1 + (γ₁/γ₀)(h/(b+h))) + ((b+h)/b − γ₁/γ₀) log(1 − (γ₁/γ₀)(b/(b+h)))]`. -/
theorem zStar_eq_ams_tildeF (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (q γ₀ γ₁ : ℝ) (hγ₀ : 0 < γ₀) (hγ₁ : γ₁ ≠ 0)
    (hlo : -((b + h) / h) < γ₁ / γ₀) (hhi : γ₁ / γ₀ < (b + h) / b) :
    ams (tildeF b h q γ₀ γ₁) q = zStar b h γ₀ γ₁ := by sorry

end DataDrivenNV.WMS
