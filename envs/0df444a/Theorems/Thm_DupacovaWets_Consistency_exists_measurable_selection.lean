-- Prove2me | Theorems.Thm_DupacovaWets_Consistency_exists_measurable_selection
-- name    : DupacovaWets.Consistency.exists_measurable_selection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T13:47:46.381408+00:00
-- url     : https://prove2.me/theorems/362ece8a-0fc7-4fbb-95be-d1f396b37b93
-- title:
--   Proposition 3.1, p. 12 — measurable selection theorem for closed-valued measurable multifunctions into ℝᵐ
-- statement:
--   Let $(T,\mathcal T)$ be a measurable space and $\Gamma:T\rightrightarrows\mathbb R^m$ a multifunction such that every $\Gamma(t)$ is closed and $\Gamma$ is measurable. Then
--
--   $$
--   \operatorname{dom}\Gamma=\{t\in T:\Gamma(t)\neq\emptyset\}=\Gamma^{-1}(\mathbb R^m)\in\mathcal T,
--   $$
--
--   and $\Gamma$ admits a measurable selector: a measurable $x$ with $x(t)\in\Gamma(t)$ for every $t\in\operatorname{dom}\Gamma$.
--
--   This is the measurable selection theorem (Kuratowski–Ryll-Nardzewski) quoted by Dupačová and Wets; in their consistency theorem it produces $\mathcal F^\nu$-measurable estimators from the measurable solution multifunctions.
--
--   **Formalization Note** The paper states it for $\Gamma:\Xi\rightrightarrows\mathbb R^n$ on the data space $(\Xi,\mathcal A)$; it is stated here over an arbitrary measurable space, because the proof of Theorem 3.9 applies it on $(Z_0,\text{trace of }\mathcal F^\nu)$. The selector is a total measurable function $x:T\to\mathbb R^m$ that selects on $\operatorname{dom}\Gamma$; since $\operatorname{dom}\Gamma$ is measurable this is equivalent to the paper's $x:\operatorname{dom}\Gamma\to\mathbb R^n$ (extend by a constant). $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)`.
-- source:
--   Dupačová & Wets, IIASA Working Paper WP-86-41 (Aug. 1986), p. 12, Proposition 3.1

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_Multifunction
open MeasureTheory

namespace DupacovaWets.Consistency

/-- Dupačová–Wets (WP-86-41), p. 12, Proposition 3.1 (measurable selections), over an arbitrary
measurable space `T`: if `Γ : T ⇉ ℝᵐ` is closed-valued and measurable, then
`dom Γ = {t | Γ(t) ≠ ∅}` is measurable and `Γ` has a measurable selector on `dom Γ`
(here a measurable `x : T → ℝᵐ` with `x(t) ∈ Γ(t)` whenever `Γ(t) ≠ ∅`). -/
theorem exists_measurable_selection {T : Type*} [MeasurableSpace T] {m : ℕ}
    (Γ : T → Set (EuclideanSpace ℝ (Fin m))) (hclosed : ∀ t, IsClosed (Γ t))
    (hmeas : IsMeasurableMultifunction Γ) :
    MeasurableSet {t | (Γ t).Nonempty} ∧
      ∃ x : T → EuclideanSpace ℝ (Fin m), Measurable x ∧ ∀ t, (Γ t).Nonempty → x t ∈ Γ t := by sorry

end DupacovaWets.Consistency
