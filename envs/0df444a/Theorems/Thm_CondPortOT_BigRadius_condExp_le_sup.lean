-- Prove2me | Theorems.Thm_CondPortOT_BigRadius_condExp_le_sup
-- name    : CondPortOT.BigRadius.condExp_le_sup
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:17:55.584868+00:00
-- url     : https://prove2.me/theorems/448ff76d-ca6d-4359-89bc-ada7cdbd5b04
-- title:
--   p. 41, proof of Proposition 3.1, used on p. 46 — E_ℚ[ℓ(Y) | (X,Y) ∈ S] ≤ sup_y ℓ(y)
-- statement:
--   Let $\mathbb Q$ be a probability measure on $\mathcal X\times\mathcal Y$, $S\subseteq\mathcal X\times\mathcal Y$ a measurable set with $\mathbb Q(S)>0$, and $\ell:\mathcal Y\to\mathbb R$ any function. Then
--   $$\mathbb E_{\mathbb Q}[\ell(Y)\mid (X,Y)\in S]\le\sup_{y\in\mathcal Y}\ell(y),$$
--   where the supremum is taken in the extended reals (it may be $+\infty$) and the conditional expectation is $\mathbb Q(S)^{-1}\big(\int_S\ell^+\,d\mathbb Q-\int_S\ell^-\,d\mathbb Q\big)$.
--
--   This is the upper half of the uninformative-solution results: a conditional expectation of a function of $Y$ can never exceed the supremum of that function over the support $\mathcal Y$.
--
--   **Formalization Note** No measurability or boundedness of $\ell$ is assumed; the integrals are lower Lebesgue integrals, so $+\infty-\infty$ is $-\infty$ under the conventions of `extIntegral`.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, p. 41, proof of Proposition 3.1 (last display); invoked in the proof of Proposition 4.2, p. 46

import Mathlib
import Definitions.Def_CondPortOT_BigRadius_Setting
open MeasureTheory RWPI.SqrtLasso ModelRiskOT.Duality

namespace CondPortOT.BigRadius

theorem condExp_le_sup {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (Q : Measure (X × Y)) [IsProbabilityMeasure Q] (S : Set (X × Y)) (hS : MeasurableSet S)
    (hQS : 0 < Q S) (L : Y → ℝ) :
    CondPortOT.SingUninf.condExp Q S L ≤ ⨆ y, (L y : EReal) := by sorry

end CondPortOT.BigRadius
