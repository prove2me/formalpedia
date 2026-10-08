-- Prove2me | Theorems.Thm_FoundationsML_Ranking_margin_bound_ranking_convex_hull_v2
-- name    : FoundationsML.Ranking.margin_bound_ranking_convex_hull_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:48.329972+00:00
-- url     : https://prove2.me/theorems/5233619a-39ed-485d-a1c1-006ef3345b46
-- title:
--   Corollary 10.4 — ranking margin bound for the convex hull (both inequalities; $m\ge1$)
-- statement:
--   **Statement (Corollary 10.4, p. 250, PDF p. 267).** Let $H$ be a set of real-valued (measurable) functions mapping into a bounded interval and $f$ a $\{-1,+1\}$-valued (measurable) preference function. Fix $\rho>0$; then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over the choice of a sample $S$ of size $m\ge1$, each of the following holds for all $h\in\mathrm{conv}(H)$:
--   $$R(h) \le \hat R_{S,\rho}(h) + \tfrac2\rho\big(R_m^{D_1}(H)+R_m^{D_2}(H)\big) + \sqrt{\tfrac{\log(1/\delta)}{2m}}, \qquad (10.17)$$
--   $$R(h) \le \hat R_{S,\rho}(h) + \tfrac2\rho\big(\hat R_{S_1}(H)+\hat R_{S_2}(H)\big) + 3\sqrt{\tfrac{\log(2/\delta)}{2m}}. \qquad (10.18)$$
--   Here $\mathrm{conv}(H)$ is the set (7.12) of Lemma 7.4 (sub-convex combinations $\sum\mu_k\le1$).
--
--   **Formalization Note.** The retired version allowed $m=0$ (every sample-dependent term is Lean's $x/0=0$), stated only (10.17), and used a convex hull with $\sum\mu_k=1$ whereas the book's $\mathrm{conv}(H)$ here is Lemma 7.4's set (7.12) with $\sum\mu_k\le1$ (corrected module `ConvHull_v2`). Changes: $m\ge1$, $\delta\in(0,1)$; both displayed inequalities, each at confidence $1-\delta$; $H$ bounded (Definition 3.1's domain); the book's standing measurability of the functions in $H$ and of $f$ (footnote 2) and of the supremum defining $\hat R_S(H)$ (footnote 3) explicit; the corrected `EmpiricalRademacherComplexity`/`RademacherComplexity` (`_v2`).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 250, Corollary 10.4 (PDF p. 267)

import Mathlib
import Definitions.Def_FoundationsML_Ranking_GeneralizationError
import Definitions.Def_FoundationsML_Ranking_EmpiricalMarginLoss
import Definitions.Def_FoundationsML_Ranking_RademacherComplexity_v2
import Definitions.Def_FoundationsML_Ranking_ConvHull_v2

open MeasureTheory

namespace FoundationsML.Ranking

/-- Corollary 10.4 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd
ed., MIT Press 2018, p. 250, PDF p. 267). Let `H` be a set of real-valued functions (bounded,
as Definition 3.1 requires) and `f` a `{−1,+1}`-valued preference function. Fix `ρ > 0`; then,
for any `δ > 0`, with probability at least `1 − δ` over the choice of a sample `S` of size
`m ≥ 1`, each of the following holds for all `h ∈ conv(H)`:
`R(h) ≤ R̂_{S,ρ}(h) + (2/ρ)(R_m^{D1}(H) + R_m^{D2}(H)) + sqrt(log(1/δ)/(2m))`   (10.17)
and `R(h) ≤ R̂_{S,ρ}(h) + (2/ρ)(R̂_{S1}(H) + R̂_{S2}(H)) + 3·sqrt(log(2/δ)/(2m))`   (10.18).

**Formalization Note.** Replaces `margin_bound_ranking_convex_hull`, which allowed `m = 0`
(every sample-dependent term is then Lean's `x / 0 = 0`), stated only (10.17), and used a
convex hull with `∑ μ_k = 1` whereas the book's `conv(H)` here is the set (7.12) of Lemma 7.4
(`∑ μ_k ≤ 1`; corrected module `ConvHull_v2`). Changes: `m ≥ 1`, `δ ∈ (0,1)`; both displayed
inequalities, each with probability at least `1 − δ`; `H` bounded (`hHb`, Definition 3.1's
domain); the book's standing measurability of the functions in `H` and of `f` (footnote 2,
p. 10) and of the supremum defining `R̂_S(H)` (footnote 3, p. 30, `hHsup`) are explicit; the
corrected `EmpiricalRademacherComplexity`/`RademacherComplexity` (`_v2`) are used. -/
theorem margin_bound_ranking_convex_hull_v2
    {X : Type*} [MeasurableSpace X] (D : Measure (X × X)) [IsProbabilityMeasure D]
    (f : X × X → ℝ) (hf : ∀ p, f p = 1 ∨ f p = -1) (hf_meas : Measurable f)
    (H : Set (X → ℝ)) (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b)
    (hHmeas : ∀ h ∈ H, Measurable h)
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (hm : 0 < m)
    (hHsup : Measurable (fun S : Fin m → X => EmpiricalRademacherComplexity H S))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ ConvHull H,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            (2 / ρ) * (RademacherComplexity (Measure.map Prod.fst D) H m +
              RademacherComplexity (Measure.map Prod.snd D) H m) +
            Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal ∧
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X × X | ∀ h ∈ ConvHull H,
        GeneralizationError D f h ≤
          EmpiricalMarginLoss ρ (fun i => (S i).1) (fun i => (S i).2) (fun i => f (S i)) h +
            (2 / ρ) * (EmpiricalRademacherComplexity H (fun i => (S i).1) +
              EmpiricalRademacherComplexity H (fun i => (S i).2)) +
            3 * Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.Ranking
