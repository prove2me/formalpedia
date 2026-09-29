-- Prove2me | Theorems.Thm_FoundationsML_PAC_finite_hypothesis_learning_bound_inconsistent
-- name    : FoundationsML.PAC.finite_hypothesis_learning_bound_inconsistent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:09:43.905545+00:00
-- url     : https://prove2.me/theorems/72dbe647-8d61-4e94-a17b-60e8e12fb6c0
-- title:
--   Theorem 2.13 — learning bound, finite H, inconsistent case (goal)
-- statement:
--   **Statement (Theorem 2.13, p. 20, PDF p. 37).** Let $H$ be a finite hypothesis set. Then,
--   for any $\delta>0$, with probability at least $1-\delta$, the following inequality holds:
--   $$\forall h \in H,\quad R(h) \le \hat R_S(h) + \sqrt{\frac{\log|H| + \log(2/\delta)}{2m}}.$$
--
--   This is the chapter's capstone generalization bound: it drops Theorem 2.5's consistency
--   requirement entirely, at the cost of an extra additive $\log|H|$ term inside the square
--   root (from a union bound over $H$ applied to Corollary 2.11's per-hypothesis Hoeffding
--   bound), and holds simultaneously for every hypothesis in $H$ — not just the one an
--   algorithm happens to return.
--
--   **Formalization Note.** As in `single_hypothesis_generalization_bound`, the sample
--   `S ~ D^m` is the identity random variable on `(Fin m → X, Measure.pi (fun _ => D))`; the
--   event bounded with probability `≥ 1-δ` is the *simultaneous* (uniform-convergence) bound
--   over every `h ∈ H`, i.e. `∀ h ∈ H, R(h) ≤ R̂_S(h) + sqrt((log|H|+log(2/δ))/(2m))`, matching
--   the book's `∀h ∈ H` inside the probability event, not a per-`h` statement outside it. No
--   upper bound on `δ` is imposed, matching the book's own unrestricted "for any δ > 0." Also
--   carries the book's standing measurability hypothesis (Definition 2.1, footnote 2, p. 10) on
--   `c` and on every `h ∈ H`, needed for the union-bound/Hoeffding argument to hold of the
--   disagreement events' actual probabilities rather than only their outer measure.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 20, Theorem 2.13 (PDF p. 37)

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory

namespace FoundationsML.PAC

/-- Theorem 2.13 (Learning bound — finite `H`, inconsistent case; goal; Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
p. 20, PDF p. 37). Let `H` be a finite hypothesis set of functions `X → Bool` and `c`
a target concept. Then, for any `δ > 0`, with probability at least `1 − δ` over an
i.i.d. sample `S ∼ D^m`, simultaneously for every `h ∈ H`,
`R(h) ≤ R̂_S(h) + sqrt((log|H| + log(2/δ)) / (2m))`.

**Formalization note.** Carries the book's standing measurability hypothesis (Definition 2.1,
footnote 2, p. 11) on `c` and on every `h ∈ H`. -/
theorem finite_hypothesis_learning_bound_inconsistent
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Finset (X → Bool)) (c : X → Bool)
    (hc_meas : Measurable c) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt ((Real.log (H.card : ℝ) + Real.log (2 / δ)) / (2 * m))}).toReal := by sorry

end FoundationsML.PAC
