-- Prove2me | Theorems.Thm_ChurnServiceMode_lemma_5_props_9_11
-- name    : ChurnServiceMode.lemma_5_props_9_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:52:38.858042+00:00
-- url     : https://prove2.me/theorems/4703e4a3-f55a-4d70-afeb-d1934c37dc82
-- title:
--   Lemma 5, properties 9–11: the erf inequalities behind Lemma 3
-- statement:
--   For real numbers $q,a,\theta$ (free variables, not the model's threshold) and $\operatorname{erfc}=1-\operatorname{erf}$:
--   1. (Property 9) if $q>a>0$,
--   $$(a^2-2)\Bigl(1+e^{q^2}\sqrt\pi\,q\bigl(\operatorname{erf}(q)-\operatorname{erf}(a-\tfrac1a)\bigr)\Bigr)-2a\,e^{q^2-(a-\frac1a)^2}q<0;$$
--   2. (Property 10) if $q>0$ and $\theta<q$,
--   $$e^{q^2}q-e^{\theta^2}\theta-e^{\theta^2+q^2}\theta q\sqrt\pi\bigl(\operatorname{erfc}(\theta)-\operatorname{erfc}(q)\bigr)\ge0;$$
--   3. (Property 11) if $q>0$ and $\theta<q$,
--   $$2e^{q^2-\theta^2}q\theta-(1+2\theta^2)\Bigl(1+e^{q^2}q\sqrt\pi\bigl(\operatorname{erfc}(\theta)-\operatorname{erfc}(q)\bigr)\Bigr)<0.$$
--
--   These three inequalities are what the proof of Lemma 3 uses to show that exactly one of the two threshold equations has a root in its range.
--
--   Differences from the source: none.
-- source:
--   Y. Kanoria, I. Lobel, J. Lu, Managing Customer Churn via Service Mode Control, SSRN 3188226 (version of December 1, 2022), https://ssrn.com/abstract=3188226, Lemma 5, properties 9–11, p.18 (PDF p.18); proofs OA A, PDF pp.36–40

import Mathlib
import Definitions.Def_ChurnServiceMode_Params

open PSOutsourcing.PartialObs (erf)

namespace ChurnServiceMode

/-- **Lemma 5, properties 9–11** (Kanoria, Lobel & Lu, *Managing Customer Churn via Service Mode Control*, SSRN 3188226 (Dec 1, 2022), p.18), with `erfc = 1 − erf` and free real variables
`q, a, θ` (not the model's threshold):
9. if `q > a > 0`: `(a² − 2)(1 + e^{q²}√π q (erf(q) − erf(a − 1/a))) − 2a e^{q² − (a − 1/a)²} q < 0`;
10. if `q > 0` and `θ < q`: `e^{q²} q − e^{θ²} θ − e^{θ² + q²} θ q √π (erfc(θ) − erfc(q)) ≥ 0`;
11. if `q > 0` and `θ < q`:
    `2 e^{q² − θ²} q θ − (1 + 2θ²)(1 + e^{q²} q √π (erfc(θ) − erfc(q))) < 0`. -/
theorem lemma_5_props_9_11 :
    (∀ q a : ℝ, 0 < a → a < q →
      (a ^ 2 - 2) * (1 + Real.exp (q ^ 2) * Real.sqrt Real.pi * q * (erf q - erf (a - 1 / a)))
        - 2 * a * Real.exp (q ^ 2 - (a - 1 / a) ^ 2) * q < 0) ∧
    (∀ q θ : ℝ, 0 < q → θ < q →
      0 ≤ Real.exp (q ^ 2) * q - Real.exp (θ ^ 2) * θ
        - Real.exp (θ ^ 2 + q ^ 2) * θ * q * Real.sqrt Real.pi * (erfc θ - erfc q)) ∧
    (∀ q θ : ℝ, 0 < q → θ < q →
      2 * Real.exp (q ^ 2 - θ ^ 2) * q * θ
        - (1 + 2 * θ ^ 2) * (1 + Real.exp (q ^ 2) * q * Real.sqrt Real.pi * (erfc θ - erfc q))
        < 0) := by sorry

end ChurnServiceMode
