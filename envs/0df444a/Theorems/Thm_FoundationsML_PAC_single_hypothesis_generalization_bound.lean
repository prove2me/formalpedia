-- Prove2me | Theorems.Thm_FoundationsML_PAC_single_hypothesis_generalization_bound
-- name    : FoundationsML.PAC.single_hypothesis_generalization_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:09:15.781966+00:00
-- url     : https://prove2.me/theorems/f6cd0d1d-8bb2-4d7d-a93d-d67f152e70fa
-- title:
--   Corollary 2.11 — generalization bound, single hypothesis
-- statement:
--   **Statement (Corollary 2.11, p. 19, PDF p. 36).** Fix a hypothesis $h : X \to \{0,1\}$.
--   Then, for any $\delta>0$, the following inequality holds with probability at least
--   $1-\delta$ (over an i.i.d. sample $S\sim D^m$):
--   $$R(h) \le \hat R_S(h) + \sqrt{\frac{\log(2/\delta)}{2m}}.$$
--
--   This is the Hoeffding-inequality step (via Theorem D.2 and Corollary 2.10) applied to a
--   single *fixed* hypothesis, which Theorem 2.13's union-bound argument then applies to every
--   hypothesis in a finite $H$ simultaneously.
--
--   **Formalization Note.** The i.i.d. sample `S ~ D^m` is modeled as the identity random
--   variable on the product-measure space `(Fin m → X, Measure.pi (fun _ => D))`, so the
--   probability statement is the `Measure.pi`-measure (cast to `ℝ`) of the event set
--   `{S | R(h) ≤ R̂_S(h) + sqrt(log(2/δ)/(2m))}`. No upper bound on `δ` is imposed, matching the
--   book's own unrestricted "for any δ > 0." Also carries the book's standing measurability
--   hypothesis (Definition 2.1, footnote 2, p. 10) on `c` and `h`, needed for the Hoeffding tail
--   bound to hold of the disagreement event's actual probability.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 19, Corollary 2.11 (PDF p. 36)

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory

namespace FoundationsML.PAC

/-- Corollary 2.11 (Generalization bound — single hypothesis; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 19, PDF p. 36).
Fix a hypothesis `h : X → Bool` and a target concept `c : X → Bool`. Then, for any `δ > 0`,
with probability at least `1 − δ` over an i.i.d. sample `S ∼ D^m`,
`R(h) ≤ R̂_S(h) + sqrt(log(2/δ) / (2m))`.

**Formalization note.** Carries the book's standing measurability hypothesis (Definition 2.1,
footnote 2, p. 11) on `c` and `h`. -/
theorem single_hypothesis_generalization_bound
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c h : X → Bool) (hc_meas : Measurable c) (hh_meas : Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c h ≤
        EmpiricalError S c h + Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.PAC
