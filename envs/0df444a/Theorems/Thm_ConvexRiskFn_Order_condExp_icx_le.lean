-- Prove2me | Theorems.Thm_ConvexRiskFn_Order_condExp_icx_le
-- name    : ConvexRiskFn.Order.condExp_icx_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:28.698912+00:00
-- url     : https://prove2.me/theorems/7c56d37f-ffed-4e1d-b5e3-e910d0e1f947
-- title:
--   Proof of Theorem 5.1, p. 446 — by Jensen's inequality, 𝔼[X | 𝒢] ⪯icx X
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $p\ge1$, $X\in\mathcal L_p(\Omega,\mathcal F,P)$ and $\mathcal G\subset\mathcal F$ a $\sigma$-algebra. Then $\mathbb E[X\mid\mathcal G]\in\mathcal L_p(\Omega,\mathcal F,P)$ and
--
--   $$\mathbb E[X\mid\mathcal G]\ \preceq_{\mathrm{icx}}\ X,$$
--
--   that is, $\mathbb E\big[u(\mathbb E[X\mid\mathcal G])\big]\le\mathbb E[u(X)]$ for every increasing convex $u:\mathbb R\to\mathbb R$ for which both expectations exist.
--
--   This is the step of the proof of Theorem 5.1 showing that consistency with $\succeq_{\mathrm{icx}}$ forces risk aversion.
--
--   **Formalization Note** The membership $\mathbb E[X\mid\mathcal G]\in\mathcal X$ is the standing assumption of §5.1 (p. 443), which holds for $\mathcal L_p$; it is stated as part of the conclusion. The conditional expectation is Mathlib's `P[X|m]`.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 446, proof of Theorem 5.1, display after "we have by Jensen's inequality that" and the sentence "Consequently, 𝔼[X | 𝒢] ⪯icx X"; p. 443, §5.1 standing assumption 𝔼[X | 𝒢] ∈ 𝒳

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_ConvexRiskFn_Order_Setting
open MeasureTheory

namespace ConvexRiskFn.Order

/-- Proof of Theorem 5.1, p. 446: by Jensen's inequality `𝔼[X | 𝒢] ⪯_icx X` for every σ-algebra
`𝒢 ⊂ ℱ`; together with the standing assumption of §5.1 (p. 443) that `𝔼[X | 𝒢] ∈ 𝒳`. -/
theorem condExp_icx_le {Ω : Type*} (m : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (hm : m ≤ mΩ) (P : Measure Ω) [IsProbabilityMeasure P] (p : ENNReal) (hp1 : 1 ≤ p)
    (X : Ω → ℝ) (hX : MemLp X p P) :
    MemLp (P[X|m]) p P ∧ StochasticOrders.MonotoneConvex.IcxOrder P P (P[X|m]) X := by sorry

end ConvexRiskFn.Order
