-- Prove2me | Theorems.Thm_BartlettBousquetMendelson_LocalRad_lemma_A_4
-- name    : BartlettBousquetMendelson.LocalRad.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:04:17.036519+00:00
-- url     : https://prove2.me/theorems/75bdff2f-3f1a-441b-99a0-9bc1392cc0b4
-- title:
--   Lemma A.4: $\mathbb ER_n\mathcal F$ versus $\mathbb E_\sigma R_n\mathcal F$ with high probability
-- statement:
--   Fix $x>0$ and let $\mathcal F$ be a class of functions with ranges in $[a,b]$; let $X_1,\dots,X_n$ be iid with law $P$. Then
--
--   1. with probability at least $1-e^{-x}$,
--   $$
--   \mathbb ER_n\mathcal F\le\inf_{\alpha\in(0,1)}\Big(\frac1{1-\alpha}\mathbb E_\sigma R_n\mathcal F+\frac{(b-a)x}{4n\alpha(1-\alpha)}\Big);
--   $$
--   2. with probability at least $1-e^{-x}$,
--   $$
--   \mathbb E_\sigma R_n\mathcal F\le\inf_{\alpha>0}\Big((1+\alpha)\mathbb ER_n\mathcal F+\frac{(b-a)x}{2n}\Big(\frac1{2\alpha}+\frac13\Big)\Big).
--   $$
--
--   The lemma lets the Rademacher average be replaced by its empirical version, at the price of the displayed terms.
--
--   Differences from the source:
--   - reading: the measurability convention of p. 7 ("we assume that the class F and the distribution P satisfy appropriate (mild) conditions for measurability of this supremum") → each f ∈ F measurable and IsPointwiseMeasurableClass F; reason: the paper leaves the convention open (refs [11, 28]); pointwise measurability (van der Vaart–Wellner §2.3.3) is a standard choice that makes every supremum over the class a countable one, and Lean integrates non-measurable functions to 0
--   - encoding: … ≤ inf_α h(α) inside the event → ∀ α in the range, … ≤ h(α) inside the event; reason: equivalent; avoids a real infimum
--   - encoding: any class F (sup over ∅ is −∞, the claim trivial) → F.Nonempty; reason: Lean's real supremum over ∅ is 0, not −∞; only the trivial case is excluded
--   - encoding: X₁, …, Xₙ independent with law P, independent Rademacher signs → sample ω : Fin n → X under Measure.pi (fun _ => P), signs averaged exactly over Fin n → Bool, 0 < n; reason: the statement depends only on the law of the sample; n ≥ 1 is implicit in 1/n
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), Lemma A.4, p. 35 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_BartlettBousquetMendelson_LocalRad_empRademacher
import Definitions.Def_BartlettBousquetMendelson_LocalRad_rademacherAvg

open MeasureTheory

namespace BartlettBousquetMendelson.LocalRad

/-- **Lemma A.4.**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), Lemma A.4, p. 35: "Fix x > 0, and let F be a class of functions with ranges in [a,b]. Then,
with probability at least 1 − e^{−x},
ERnF ≤ inf_{α∈(0,1)} ( (1/(1 − α)) EσRnF + (b − a)x/(4nα(1 − α)) ).
Also, with probability at least 1 − e^{−x},
EσRnF ≤ inf_{α>0} ( (1 + α)ERnF + ((b − a)x/(2n)) (1/(2α) + 1/3) )."

For a nonempty class `F` of measurable functions with ranges in `[a, b]`, `n ≥ 1` and `x > 0`,
over an iid sample `X₁, …, Xₙ ~ P`: (1) with probability at least `1 − e^{−x}`, for every
`α ∈ (0, 1)`, `E Rₙ F ≤ E_σ Rₙ F/(1 − α) + (b − a)x/(4nα(1 − α))`; (2) with probability at
least `1 − e^{−x}`, for every `α > 0`, `E_σ Rₙ F ≤ (1 + α) E Rₙ F + ((b − a)x/(2n))(1/(2α) + 1/3)`.

**Formalization Note.** "`… ≤ inf_α h(α)`" inside the event is written "for every `α`,
`… ≤ h(α)`", which is equivalent and avoids a real infimum. Measurability: each `f` measurable
and `F` pointwise measurable (Reading M). `F` nonempty: the paper's supremum over the empty class
is `−∞`; Lean's is `0`. -/
theorem lemma_A_4 {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (F : Set (X → ℝ)) (a b : ℝ) (n : ℕ) (hn : 0 < n) (hne : F.Nonempty)
    (hmeas : ∀ f ∈ F, Measurable f) (hpm : IsPointwiseMeasurableClass F)
    (hrange : ∀ f ∈ F, ∀ y, f y ∈ Set.Icc a b) (x : ℝ) (hx : 0 < x) :
    1 - Real.exp (-x) ≤ (Measure.pi fun _ : Fin n => P).real {ω | ∀ α : ℝ, 0 < α → α < 1 →
        rademacherAvg P n F ≤
          1 / (1 - α) * empRademacher n F ω + (b - a) * x / (4 * n * α * (1 - α))} ∧
    1 - Real.exp (-x) ≤ (Measure.pi fun _ : Fin n => P).real {ω | ∀ α : ℝ, 0 < α →
        empRademacher n F ω ≤
          (1 + α) * rademacherAvg P n F + (b - a) * x / (2 * n) * (1 / (2 * α) + 1 / 3)} := by sorry

end BartlettBousquetMendelson.LocalRad
