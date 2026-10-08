-- Prove2me | Theorems.Thm_FoundationsML_Boosting_ensemble_rademacher_margin_bound_v2
-- name    : FoundationsML.Boosting.ensemble_rademacher_margin_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:04.629447+00:00
-- url     : https://prove2.me/theorems/1e69e9a4-99a5-4c07-b185-162ef2c9ca84
-- title:
--   Corollary 7.5 — ensemble Rademacher margin bound (labels $\pm1$, $m\ge1$)
-- statement:
--   **Statement (Corollary 7.5, p. 158, PDF p. 175).** Let $H$ denote a set of real-valued (measurable) functions mapping into a bounded interval and $D$ a distribution over $X\times\{-1,+1\}$. Fix $\rho>0$. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample of size $m\ge1$, each of the following holds for all $h\in\mathrm{conv}(H)$:
--   $$R(h) \le \hat R_{S,\rho}(h) + \frac2\rho R_m(H) + \sqrt{\frac{\log(1/\delta)}{2m}}, \qquad (7.13)$$
--   $$R(h) \le \hat R_{S,\rho}(h) + \frac2\rho \hat R_S(H) + 3\sqrt{\frac{\log(2/\delta)}{2m}}. \qquad (7.14)$$
--   Each inequality holds with probability at least $1-\delta$; $\mathrm{conv}(H)$ is the set (7.12).
--
--   **Formalization Note.** The retired version allowed $m=0$ (every sample-dependent term is Lean's $x/0=0$). Changes, exactly as for Theorem 5.8 which this corollary applies to $\mathrm{conv}(H)$ via Lemma 7.4: $m\ge1$, $\delta\in(0,1)$; labels in $\{-1,+1\}$ $D$-a.s.; $H$ bounded (Definition 3.1's domain for $R_m(H)$); the book's standing measurability of the functions in $H$ (footnote 2 — elements of $\mathrm{conv}(H)$ are finite combinations of them) and of the supremum defining $\hat R_S(H)$ (footnote 3) explicit; the corrected `EmpiricalRademacherComplexity`/`RademacherComplexity` (`_v2`); and the two inequalities each asserted at confidence $1-\delta$ instead of both inside one event. $D.\mathrm{map}\,\mathrm{Prod.fst}$ is the marginal on $X$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 158, Corollary 7.5 (PDF p. 175)

import Mathlib
import Definitions.Def_FoundationsML_Boosting_MarginGeneralizationError
import Definitions.Def_FoundationsML_Boosting_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Boosting_RademacherComplexity_v2
import Definitions.Def_FoundationsML_Boosting_ConvHull

open MeasureTheory

namespace FoundationsML.Boosting

/-- Corollary 7.5 (Ensemble Rademacher margin bound; Mohri, Rostamizadeh & Talwalkar,
*Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 158, PDF p. 175). Let `H` denote
a set of real-valued functions (bounded, as Definition 3.1 requires) and `D` a distribution
over `X × {−1,+1}`. Fix `ρ > 0`; then, for any `δ > 0`, with probability at least `1 − δ` over
an i.i.d. sample of size `m ≥ 1`, each of the following holds for all `h ∈ conv(H)`:
`R(h) ≤ R̂_{S,ρ}(h) + (2/ρ) R_m(H) + sqrt(log(1/δ)/(2m))`   (7.13)
and `R(h) ≤ R̂_{S,ρ}(h) + (2/ρ) R̂_S(H) + 3·sqrt(log(2/δ)/(2m))`   (7.14).

**Formalization Note.** Replaces `ensemble_rademacher_margin_bound`, which allowed `m = 0`
(every sample-dependent term is then Lean's `x / 0 = 0`). Changes: `m ≥ 1`, `δ ∈ (0,1)`
(standing conventions); labels in `{−1,+1}` `D`-almost surely (`hDy`, the binary setting of
Theorem 5.8 which this corollary applies to `conv(H)`); `H` maps into a bounded interval
(`hHb`, Definition 3.1's domain for `R_m(H)`); the book's standing measurability of the
functions in `H` (footnote 2, p. 10 — elements of `conv(H)` are finite combinations of them)
and of the supremum defining `R̂_S(H)` (footnote 3, p. 30, `hHsup`) are explicit; the corrected
`EmpiricalRademacherComplexity`/`RademacherComplexity` (`_v2`) are used; and the two
inequalities are each asserted with probability at least `1 − δ`, as the book proves them
(the retired version demanded both inside one `1 − δ` event). `conv(H)` is the set (7.12);
`D.map Prod.fst` is the marginal of `D` on `X`. -/
theorem ensemble_rademacher_margin_bound_v2
    {X : Type*} [MeasurableSpace X] (D : Measure (X × ℝ)) [IsProbabilityMeasure D]
    (hDy : ∀ᵐ p ∂D, p.2 = 1 ∨ p.2 = -1)
    (H : Set (X → ℝ)) (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b)
    (hHmeas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (hm : 0 < m)
    (hHsup : Measurable (fun S : Fin m → X => EmpiricalRademacherComplexity H S))
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ ConvHull H,
        MarginGeneralizationError D h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
            (2 / ρ) * RademacherComplexity (D.map Prod.fst) H m +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × ℝ | ∀ h ∈ ConvHull H,
        MarginGeneralizationError D h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) h +
            (2 / ρ) * EmpiricalRademacherComplexity H (fun i => (S i).1) +
            3 * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Boosting
