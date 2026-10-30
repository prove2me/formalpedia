-- Prove2me | Theorems.Thm_BartlettBousquetMendelson_LocalRad_theorem_2_1
-- name    : BartlettBousquetMendelson.LocalRad.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:04:56.169621+00:00
-- url     : https://prove2.me/theorems/df391a46-a03a-452e-8b5b-dafb02d6900c
-- title:
--   Theorem 2.1: variance-sensitive uniform deviation bounds
-- statement:
--   Let $\mathcal F$ be a class of functions mapping $\mathcal X$ into $[a,b]$, and suppose $\mathrm{Var}[f(X_i)]\le r$ for every $f\in\mathcal F$, for some $r>0$. Let $X_1,\dots,X_n$ be iid with law $P$. Then for every $x>0$:
--
--   1. with probability at least $1-e^{-x}$,
--   $$
--   \sup_{f\in\mathcal F}(Pf-P_nf)\le\inf_{\alpha>0}\Big(2(1+\alpha)\mathbb ER_n\mathcal F+\sqrt{\frac{2rx}n}+(b-a)\Big(\frac13+\frac1\alpha\Big)\frac xn\Big);
--   $$
--   2. with probability at least $1-2e^{-x}$,
--   $$
--   \sup_{f\in\mathcal F}(Pf-P_nf)\le\inf_{\alpha\in(0,1)}\Big(2\frac{1+\alpha}{1-\alpha}\mathbb E_\sigma R_n\mathcal F+\sqrt{\frac{2rx}n}+(b-a)\Big(\frac13+\frac1\alpha+\frac{1+\alpha}{2\alpha(1-\alpha)}\Big)\frac xn\Big);
--   $$
--   3. the same two bounds hold for $\sup_{f\in\mathcal F}(P_nf-Pf)$.
--
--   The variance bound $r$ in the square-root term is what the localization argument of Section 3 exploits.
--
--   Differences from the source:
--   - reading: the measurability convention of p. 7 ("we assume that the class F and the distribution P satisfy appropriate (mild) conditions for measurability of this supremum") → each f ∈ F measurable and IsPointwiseMeasurableClass F; reason: the paper leaves the convention open (refs [11, 28]); pointwise measurability (van der Vaart–Wellner §2.3.3) is a standard choice that makes every supremum over the class a countable one, and Lean integrates non-measurable functions to 0
--   - encoding: "the same results hold for sup(Pₙf − Pf)" → two further conjuncts, with supDevNeg in place of supDev, each with its own probability bound; reason: the four probability statements are stated separately, not merged into one event
--   - encoding: … ≤ inf_α h(α) inside the event → ∀ α in the range, … ≤ h(α) inside the event; reason: equivalent; avoids a real infimum
--   - encoding: any class F (sup over ∅ is −∞, the claim trivial) → F.Nonempty; reason: Lean's real supremum over ∅ is 0, not −∞; only the trivial case is excluded
--   - encoding: X₁, …, Xₙ independent with law P, independent Rademacher signs → sample ω : Fin n → X under Measure.pi (fun _ => P), signs averaged exactly over Fin n → Bool, 0 < n; reason: the statement depends only on the law of the sample; n ≥ 1 is implicit in 1/n
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), Theorem 2.1, p. 8 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_BartlettBousquetMendelson_LocalRad_empRademacher
import Definitions.Def_BartlettBousquetMendelson_LocalRad_rademacherAvg
import Definitions.Def_BartlettBousquetMendelson_LocalRad_supDev
import Definitions.Def_BartlettBousquetMendelson_LocalRad_supDevNeg

open MeasureTheory ProbabilityTheory

namespace BartlettBousquetMendelson.LocalRad

/-- **Theorem 2.1.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), Theorem 2.1, p. 8: "Let F be a class of functions that map X into [a,b]. Assume that there is
some r > 0 such that for every f ∈ F, Var[f(Xi)] ≤ r. Then, for every x > 0, with probability at
least 1 − e^{−x},
sup_{f∈F}(Pf − Pnf) ≤ inf_{α>0} ( 2(1 + α)ERnF + √(2rx/n) + (b − a)(1/3 + 1/α)(x/n) ),
and with probability at least 1 − 2e^{−x},
sup_{f∈F}(Pf − Pnf) ≤ inf_{α∈(0,1)} ( 2((1 + α)/(1 − α))EσRnF + √(2rx/n)
+ (b − a)(1/3 + 1/α + (1 + α)/(2α(1 − α)))(x/n) ).
Moreover, the same results hold for the quantity sup_{f∈F}(Pnf − Pf)."

For a nonempty class `F` of measurable functions with ranges in `[a, b]` and `Var f ≤ r`
(`r > 0`), `n ≥ 1` and every `x > 0`, over an iid sample `X₁, …, Xₙ ~ P`, four probability
bounds hold: the first display (probability `≥ 1 − e^{−x}`, every `α > 0`) and the second
display (probability `≥ 1 − 2e^{−x}`, every `α ∈ (0, 1)`), each for `V⁺ = sup_f (Pf − Pₙf)`
(`supDev`) and for `V⁻ = sup_f (Pₙf − Pf)` (`supDevNeg`).

**Formalization Note.** "`… ≤ inf_α h(α)`" inside an event is written "for every `α`,
`… ≤ h(α)`" (equivalent). Each of the four claims has its own probability bound; they are not
merged into one event. Measurability: each `f` measurable and `F` pointwise measurable
(Reading M). `F` nonempty: the paper's supremum over the empty class is `−∞` and the claims are
then trivial; Lean's is `0`. -/
theorem theorem_2_1 {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (F : Set (X → ℝ)) (a b r : ℝ) (n : ℕ) (hn : 0 < n) (hne : F.Nonempty)
    (hmeas : ∀ f ∈ F, Measurable f) (hpm : IsPointwiseMeasurableClass F)
    (hrange : ∀ f ∈ F, ∀ y, f y ∈ Set.Icc a b) (hr : 0 < r)
    (hvar : ∀ f ∈ F, variance f P ≤ r) :
    ∀ x : ℝ, 0 < x →
      (1 - Real.exp (-x) ≤ (Measure.pi fun _ : Fin n => P).real {ω | ∀ α : ℝ, 0 < α →
          supDev P n F ω ≤ 2 * (1 + α) * rademacherAvg P n F + Real.sqrt (2 * r * x / n)
            + (b - a) * (1 / 3 + 1 / α) * (x / n)}) ∧
      (1 - 2 * Real.exp (-x) ≤ (Measure.pi fun _ : Fin n => P).real {ω | ∀ α : ℝ, 0 < α → α < 1 →
          supDev P n F ω ≤ 2 * ((1 + α) / (1 - α)) * empRademacher n F ω
            + Real.sqrt (2 * r * x / n)
            + (b - a) * (1 / 3 + 1 / α + (1 + α) / (2 * α * (1 - α))) * (x / n)}) ∧
      (1 - Real.exp (-x) ≤ (Measure.pi fun _ : Fin n => P).real {ω | ∀ α : ℝ, 0 < α →
          supDevNeg P n F ω ≤ 2 * (1 + α) * rademacherAvg P n F + Real.sqrt (2 * r * x / n)
            + (b - a) * (1 / 3 + 1 / α) * (x / n)}) ∧
      (1 - 2 * Real.exp (-x) ≤ (Measure.pi fun _ : Fin n => P).real {ω | ∀ α : ℝ, 0 < α → α < 1 →
          supDevNeg P n F ω ≤ 2 * ((1 + α) / (1 - α)) * empRademacher n F ω
            + Real.sqrt (2 * r * x / n)
            + (b - a) * (1 / 3 + 1 / α + (1 + α) / (2 * α * (1 - α))) * (x / n)}) := by sorry

end BartlettBousquetMendelson.LocalRad
