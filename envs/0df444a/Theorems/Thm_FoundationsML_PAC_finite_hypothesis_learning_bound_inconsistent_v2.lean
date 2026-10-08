-- Prove2me | Theorems.Thm_FoundationsML_PAC_finite_hypothesis_learning_bound_inconsistent_v2
-- name    : FoundationsML.PAC.finite_hypothesis_learning_bound_inconsistent_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:19.54599+00:00
-- url     : https://prove2.me/theorems/250f3975-56d7-4fa1-8b50-4c9172cf64ac
-- title:
--   Theorem 2.13 — learning bound, finite $H$, inconsistent case ($m\ge1$; goal)
-- statement:
--   **Statement (Theorem 2.13, p. 20, PDF p. 37).** Let $H$ be a finite nonempty hypothesis set. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample $S\sim D^m$ of size $m\ge1$, the following inequality holds:
--   $$\forall h \in H,\quad R(h) \le \hat R_S(h) + \sqrt{\frac{\log|H| + \log(2/\delta)}{2m}}.$$
--   The bound holds simultaneously for every $h\in H$ (uniform convergence), by a union bound over $H$ applied to Corollary 2.11.
--
--   **Formalization Note.** The retired version allowed the degenerate sample size $m=0$, where Lean's $x/0=0$ zeroes the empirical error and the deviation term and the bound is false. The new statement requires $m\ge1$, $\delta\in(0,1)$ and $H\neq\emptyset$, the book's standing conventions for a sample of size $m$, a confidence parameter and a hypothesis set. The $\forall h\in H$ stays inside the probability event; the book's standing measurability hypothesis (Definition 2.1, footnote 2, p. 10) on $c$ and on every $h\in H$ is carried explicitly (with `Bool` carrying the discrete σ-algebra the error events are then measurable).
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 20, Theorem 2.13 (PDF p. 37)

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory

namespace FoundationsML.PAC

/-- Theorem 2.13 (Learning bound — finite `H`, inconsistent case; goal; Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
p. 20, PDF p. 37). Let `H` be a finite (nonempty) hypothesis set of functions `X → Bool` and
`c` a target concept. Then, for any `δ > 0`, with probability at least `1 − δ` over an
i.i.d. sample `S ∼ D^m` of size `m ≥ 1`, simultaneously for every `h ∈ H`,
`R(h) ≤ R̂_S(h) + sqrt((log|H| + log(2/δ)) / (2m))`.

**Formalization Note.** Replaces `finite_hypothesis_learning_bound_inconsistent`, which
allowed the degenerate sample size `m = 0` (Lean's `x / 0 = 0` zeroes the empirical error and
the deviation term, making the bound false). Now `m ≥ 1`, `δ ∈ (0,1)` and `H ≠ ∅`, the book's
standing conventions for a sample of size `m`, a confidence level and a hypothesis set.
Carries the book's standing measurability hypothesis (Definition 2.1, footnote 2, p. 10) on
`c` and on every `h ∈ H`. -/
theorem finite_hypothesis_learning_bound_inconsistent_v2
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Finset (X → Bool)) (hHne : H.Nonempty) (c : X → Bool)
    (hc_meas : Measurable c) (hH_meas : ∀ h ∈ H, Measurable h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt ((Real.log (H.card : ℝ) + Real.log (2 / δ)) / (2 * m))}).toReal := by sorry

end FoundationsML.PAC
