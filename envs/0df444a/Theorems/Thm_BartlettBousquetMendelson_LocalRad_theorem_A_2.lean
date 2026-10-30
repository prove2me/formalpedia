-- Prove2me | Theorems.Thm_BartlettBousquetMendelson_LocalRad_theorem_A_2
-- name    : BartlettBousquetMendelson.LocalRad.theorem_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:03:46.020767+00:00
-- url     : https://prove2.me/theorems/52194b08-b8b6-48f8-af60-f55c3ff9e0a2
-- title:
--   Theorem A.2: concentration of $n\mathbb E_\sigma R_n\mathcal F$ (corrected: strict inequalities in the tail events)
-- statement:
--   Let $\mathcal F$ be a nonempty class of measurable functions mapping $\mathcal X$ into $[a,b]$, let $X_1,\dots,X_n$ be iid with law $P$, and let
--
--   $$
--   Z=\mathbb E_\sigma\sup_{f\in\mathcal F}\sum_{i=1}^n\sigma_if(X_i)=n\,\mathbb E_\sigma R_n\mathcal F.
--   $$
--
--   Then for every $x\ge0$:
--
--   1. $$\Pr\Big(Z>\mathbb EZ+\sqrt{(b-a)x\,\mathbb EZ}+\frac{(b-a)x}6\Big)\le e^{-x};$$
--   2. $$\Pr\Big(Z<\mathbb EZ-\sqrt{(b-a)x\,\mathbb EZ}\Big)\le e^{-x}.$$
--
--   The empirical Rademacher average concentrates around its mean; this is what makes the data-dependent second display of Theorem 2.1 possible.
--
--   Differences from the source:
--   - correction: Pr(Z ≥ EZ + √((b − a)xEZ) + (b − a)x/6) ≤ e^{−x} and Pr(Z ≤ EZ − √((b − a)xEZ)) ≤ e^{−x} → the same with strict inequalities Z > … and Z < … inside the probabilities; reason: the printed tails fail when Z is constant: for F = {f} a single function Z = 0 and EZ = 0, so Pr(Z ≤ EZ − 0) = 1 > e^{−x} for x > 0 (and for b = a also Pr(Z ≥ EZ) = 1); when b > a (and EZ > 0 for the lower tail) the thresholds are continuous and strictly monotone in x, so the strict and printed forms are equivalent
--   - reading: the measurability convention of p. 7 ("we assume that the class F and the distribution P satisfy appropriate (mild) conditions for measurability of this supremum") → each f ∈ F measurable and IsPointwiseMeasurableClass F; reason: the paper leaves the convention open (refs [11, 28]); pointwise measurability (van der Vaart–Wellner §2.3.3) is a standard choice that makes every supremum over the class a countable one, and Lean integrates non-measurable functions to 0
--   - encoding: any class F (sup over ∅ is −∞, the claim trivial) → F.Nonempty; reason: Lean's real supremum over ∅ is 0, not −∞; only the trivial case is excluded
--   - encoding: X₁, …, Xₙ independent with law P, independent Rademacher signs → sample ω : Fin n → X under Measure.pi (fun _ => P), signs averaged exactly over Fin n → Bool, 0 < n; reason: the statement depends only on the law of the sample; n ≥ 1 is implicit in 1/n
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), Theorem A.2, p. 34 (cited from Boucheron, Lugosi, Massart [5]) (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_BartlettBousquetMendelson_LocalRad_empRademacher

open MeasureTheory

namespace BartlettBousquetMendelson.LocalRad

/-- **Theorem A.2 (concentration of the empirical Rademacher average, cited from [5])
(corrected: strict inequalities inside the probabilities).**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), Theorem A.2, p. 34: "Let F be a class of functions that map X into [a,b]. Let
Z = Eσ sup_{f∈F} Σ_{i=1}^n σif(Xi) = nEσRnF. Then for all x ≥ 0,
Pr(Z ≥ EZ + √((b − a)xEZ) + (b − a)x/6) ≤ e^{−x} and Pr(Z ≤ EZ − √((b − a)xEZ)) ≤ e^{−x}."

For a nonempty class `F` of measurable functions with ranges in `[a, b]`, `n ≥ 1`, an iid
sample `X₁, …, Xₙ ~ P` and `Z = n E_σ Rₙ F`, for every `x ≥ 0`:
(1) `Pr(Z > EZ + √((b − a) x EZ) + (b − a)x/6) ≤ e^{−x}`;
(2) `Pr(Z < EZ − √((b − a) x EZ)) ≤ e^{−x}`.

**Formalization Note.** Correction: as printed (with `≥` and `≤` inside the probabilities) both
tails fail when `Z` is constant: for `F = {f}` a single function, `Z = Σᵢ E_σ σᵢ f(Xᵢ) = 0`,
`EZ = 0`, and `Pr(Z ≤ EZ − 0) = 1 > e^{−x}` for every `x > 0`; for `b = a` also
`Pr(Z ≥ EZ + 0 + 0) = 1`. With strict inequalities the degenerate cases hold, and when `b > a`
and `EZ > 0` (resp. `b > a`) the corrected and printed tails are equivalent: the thresholds are
strictly monotone and continuous in `x`, so the printed tail at `x` is the limit of the strict
tails at `x' ↑ x`. Measurability: each `f` measurable and `F` pointwise measurable
(Reading M). `F` nonempty: the paper's supremum over the empty class is `−∞`; Lean's is `0`. -/
theorem theorem_A_2 {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (F : Set (X → ℝ)) (a b : ℝ) (n : ℕ) (hn : 0 < n) (hne : F.Nonempty)
    (hmeas : ∀ f ∈ F, Measurable f) (hpm : IsPointwiseMeasurableClass F)
    (hrange : ∀ f ∈ F, ∀ y, f y ∈ Set.Icc a b) :
    let μ : Measure (Fin n → X) := Measure.pi fun _ : Fin n => P
    let Z : (Fin n → X) → ℝ := fun ω => n * empRademacher n F ω
    let EZ : ℝ := ∫ ω, Z ω ∂μ
    ∀ x : ℝ, 0 ≤ x →
      μ.real {ω | EZ + Real.sqrt ((b - a) * x * EZ) + (b - a) * x / 6 < Z ω} ≤ Real.exp (-x) ∧
      μ.real {ω | Z ω < EZ - Real.sqrt ((b - a) * x * EZ)} ≤ Real.exp (-x) := by sorry

end BartlettBousquetMendelson.LocalRad
