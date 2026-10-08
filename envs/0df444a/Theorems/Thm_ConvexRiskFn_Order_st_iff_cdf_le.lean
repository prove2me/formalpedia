-- Prove2me | Theorems.Thm_ConvexRiskFn_Order_st_iff_cdf_le
-- name    : ConvexRiskFn.Order.st_iff_cdf_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T06:38:35.511221+00:00
-- url     : https://prove2.me/theorems/77b9ca85-1028-4095-94a5-ab8be3cfbf47
-- title:
--   §5.2, p. 445 — X₂ ⪰st X₁ iff F_{X₂}(t) ≤ F_{X₁}(t) for all t
-- statement:
--   Let $X_1,X_2$ be real random variables on a probability space $(\Omega,\mathcal F,P)$, with cdfs $F_{X_i}(t)=P(X_i\le t)$. Recall that $X_2\succeq_{\mathrm{st}}X_1$ means $\mathbb E[u(X_2)]\ge\mathbb E[u(X_1)]$ for every nondecreasing $u:\mathbb R\to\mathbb R$ for which both expectations exist. Then
--
--   $$X_2\succeq_{\mathrm{st}}X_1\quad\Longleftrightarrow\quad F_{X_2}(t)\le F_{X_1}(t)\ \text{ for all } t\in\mathbb R.$$
--
--   The paper quotes this characterization (Müller and Stoyan, Theorem 1.2.8) and uses the forward direction in the proof of Lemma 5.1.
--
--   **Formalization Note** "The expectations exist" is integrability of $u\circ X_1$ and $u\circ X_2$. The cdf inequality is stated between the measures $P\{X_2\le t\}\le P\{X_1\le t\}$.
-- source:
--   Ruszczyński, Shapiro, Optimization of convex risk functions, Math. Oper. Res. 31 (2006), p. 445, §5.2, sentence "It is possible to show that X₂ ⪰st X₁ iff …"

import Mathlib
import Definitions.Def_StochasticOrders_MonotoneConvex_IcxOrder
import Definitions.Def_ConvexRiskFn_Order_Setting
open MeasureTheory

namespace ConvexRiskFn.Order

/-- §5.2, p. 445: `X₂ ⪰_st X₁` iff `F_{X₂}(t) ≤ F_{X₁}(t)` for all `t ∈ ℝ`
(Müller and Stoyan, Theorem 1.2.8). -/
theorem st_iff_cdf_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₁ X₂ : Ω → ℝ) (h₁ : Measurable X₁) (h₂ : Measurable X₂) :
    StLE P X₁ X₂ ↔ ∀ t : ℝ, P {ω | X₂ ω ≤ t} ≤ P {ω | X₁ ω ≤ t} := by sorry

end ConvexRiskFn.Order
