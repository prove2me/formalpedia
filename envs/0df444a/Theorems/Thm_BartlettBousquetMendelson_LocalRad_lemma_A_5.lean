-- Prove2me | Theorems.Thm_BartlettBousquetMendelson_LocalRad_lemma_A_5
-- name    : BartlettBousquetMendelson.LocalRad.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:03:12.28487+00:00
-- url     : https://prove2.me/theorems/745cc44a-816d-4e47-87eb-0e5df381d5f2
-- title:
--   Lemma A.5: symmetrization, $\max(\mathbb E\sup(Pf-P_nf),\mathbb E\sup(P_nf-Pf))\le2\mathbb ER_n\mathcal F$
-- statement:
--   For a class $\mathcal F$ of functions and an iid sample $X_1,\dots,X_n\sim P$,
--
--   $$
--   \max\Big(\mathbb E\sup_{f\in\mathcal F}(Pf-P_nf),\ \mathbb E\sup_{f\in\mathcal F}(P_nf-Pf)\Big)\le2\,\mathbb ER_n\mathcal F.
--   $$
--
--   The expected uniform deviation between true and empirical means is controlled by the Rademacher average of the class.
--
--   Differences from the source:
--   - reading: the measurability convention of p. 7 ("we assume that the class F and the distribution P satisfy appropriate (mild) conditions for measurability of this supremum") → each f ∈ F measurable and IsPointwiseMeasurableClass F; reason: the paper leaves the convention open (refs [11, 28]); pointwise measurability (van der Vaart–Wellner §2.3.3) is a standard choice that makes every supremum over the class a countable one, and Lean integrates non-measurable functions to 0
--   - encoding: "for any class of functions F" (Pf defined; the claim trivial when E Rₙ F = +∞) → each f integrable; for a.e. sample the vectors (f(X₁), …, f(Xₙ)), f ∈ F, form a bounded set; E_σ Rₙ F integrable; reason: these say exactly that Pf exists and the right side is finite (a finite supremum over all 2ⁿ sign vectors bounds the vector set); Lean's real sup and Bochner integral would otherwise return 0
--   - encoding: any class F (sup over ∅ is −∞, the claim trivial) → F.Nonempty; reason: Lean's real supremum over ∅ is 0, not −∞; only the trivial case is excluded
--   - encoding: X₁, …, Xₙ independent with law P, independent Rademacher signs → sample ω : Fin n → X under Measure.pi (fun _ => P), signs averaged exactly over Fin n → Bool, 0 < n; reason: the statement depends only on the law of the sample; n ≥ 1 is implicit in 1/n
-- source:
--   Bartlett, Bousquet, Mendelson, Local Rademacher Complexities, Ann. Statist. 33(4) (2005), Lemma A.5, p. 35 (IMS electronic reprint, arXiv:math/0508275v1)

import Mathlib
import Definitions.Def_BartlettBousquetMendelson_LocalRad_IsPointwiseMeasurableClass
import Definitions.Def_BartlettBousquetMendelson_LocalRad_empRademacher
import Definitions.Def_BartlettBousquetMendelson_LocalRad_rademacherAvg
import Definitions.Def_BartlettBousquetMendelson_LocalRad_supDev
import Definitions.Def_BartlettBousquetMendelson_LocalRad_supDevNeg

open MeasureTheory

namespace BartlettBousquetMendelson.LocalRad

/-- **Lemma A.5 (symmetrization).**
Bartlett, Bousquet, Mendelson, *Local Rademacher Complexities*, Ann. Statist. 33(4) (2005) (IMS electronic reprint, arXiv:math/0508275v1), Lemma A.5, p. 35: "For any class of functions F,
max(E sup_{f∈F}(Pf − Pnf), E sup_{f∈F}(Pnf − Pf)) ≤ 2ERnF."

For a nonempty class `F` of integrable measurable functions and `n ≥ 1`,
`max(E sup_f (Pf − Pₙf), E sup_f (Pₙf − Pf)) ≤ 2 E Rₙ F`, the expectations over an iid
sample `X₁, …, Xₙ ~ P`.

**Formalization Note.** Each expectation is a Bochner integral over `Fin n → X` with
`Measure.pi`. "Any class" presupposes that `Pf` exists (each `f` integrable) and the claim
is trivial when its right side `2 E Rₙ F` is `+∞`; the Lean statement assumes that right side
finite: for almost every sample the vectors `(f(X₁), …, f(Xₙ))`, `f ∈ F`, form a bounded set (so
every supremum over sign vectors is finite), and `E_σ Rₙ F` is integrable. Measurability: each
`f` measurable and `F` pointwise measurable (Reading M). `F` nonempty: the paper's supremum
over the empty class is `−∞` and the claim is then trivial; Lean's is `0`. -/
theorem lemma_A_5 {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (F : Set (X → ℝ)) (n : ℕ) (hn : 0 < n) (hne : F.Nonempty)
    (hmeas : ∀ f ∈ F, Measurable f) (hpm : IsPointwiseMeasurableClass F)
    (hint : ∀ f ∈ F, Integrable f P)
    (hbdd : ∀ᵐ ω ∂(Measure.pi fun _ : Fin n => P),
      Bornology.IsBounded ((fun f : X → ℝ => fun i : Fin n => f (ω i)) '' F))
    (hR : Integrable (empRademacher n F) (Measure.pi fun _ : Fin n => P)) :
    max (∫ ω, supDev P n F ω ∂(Measure.pi fun _ : Fin n => P))
        (∫ ω, supDevNeg P n F ω ∂(Measure.pi fun _ : Fin n => P)) ≤
      2 * rademacherAvg P n F := by sorry

end BartlettBousquetMendelson.LocalRad
