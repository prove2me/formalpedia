-- Prove2me | Theorems.Thm_FoundationsML_PAC_finite_consistent_learning_bound
-- name    : FoundationsML.PAC.finite_consistent_learning_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T21:08:34.727898+00:00
-- url     : https://prove2.me/theorems/83411db4-f224-4a34-bf03-ded409ac1d5e
-- title:
--   Theorem 2.5 — learning bound, finite H, consistent case
-- statement:
--   **Statement (Theorem 2.5, p. 15, PDF p. 32).** Let $H$ be a finite set of functions
--   mapping from $X$ to $Y$. Let $A$ be an algorithm that, for any target concept $c \in H$
--   and i.i.d. sample $S$, returns a consistent hypothesis $h_S$: $\hat R_S(h_S) = 0$. Then,
--   for any $\epsilon,\delta>0$, the inequality $\Pr_{S\sim D^m}[R(h_S)\le\epsilon]\ge1-\delta$
--   holds if
--   $$m \ge \frac1\epsilon\Big(\log|H| + \log\frac1\delta\Big).$$
--
--   This is the chapter's first general learning guarantee: whenever a finite hypothesis set
--   admits a consistent algorithm, PAC-learnability follows with a sample complexity only
--   logarithmic in $|H|$.
--
--   **Formalization Note.** `A` is modeled as `∀ m, (Fin m → X) → (X → Y)` together with two
--   hypotheses making precise "returns a consistent hypothesis $h_S \in H$": `A m S ∈ H` for
--   every sample, and `EmpiricalError S c (A m S) = 0`. The sample-complexity condition
--   `m ≥ (1/ε)(log|H|+log(1/δ))` is stated in the equivalent multiplied-out form
--   `log|H| + log(1/δ) ≤ ε·m` to avoid a division by `ε` on the hypothesis side; no upper bound
--   on `δ` is imposed, matching the book's own unrestricted "for any ε, δ > 0."
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 15, Theorem 2.5 (PDF p. 32)

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory

namespace FoundationsML.PAC

/-- Theorem 2.5 (Learning bound — finite `H`, consistent case; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 15, PDF p. 32).
Let `H` be a finite set of functions mapping from `X` to `Y`. Let `A` be an algorithm that,
for the target concept `c ∈ H`, returns on any i.i.d. sample `S` of size `m` a hypothesis
`A m S ∈ H` consistent with `c` (`R̂_S(A m S) = 0`). Then, for any `ε, δ > 0`, the inequality
`P_{S∼D^m}[R(A m S) ≤ ε] ≥ 1 − δ` holds whenever `m ≥ (1/ε)(log|H| + log(1/δ))`.

**Formalization note.** Carries the book's standing measurability hypothesis (Definition 2.1,
footnote 2, p. 11: "the family of functions `H` and the target concept `c` must be
measurable") on `c` and on every `h ∈ H` — the latter covers `A m S` since `hA_mem` already
places it in `H`. -/
theorem finite_consistent_learning_bound
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (H : Finset (X → Y)) (D : Measure X)
    [IsProbabilityMeasure D] (c : X → Y) (hc : c ∈ H)
    (hc_meas : Measurable c) (hH_meas : ∀ h ∈ H, Measurable h)
    (A : ∀ m : ℕ, (Fin m → X) → (X → Y))
    (hA_mem : ∀ m (S : Fin m → X), A m S ∈ H)
    (hA_consistent : ∀ m (S : Fin m → X), EmpiricalError S c (A m S) = 0)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ)
    (m : ℕ) (hm : Real.log (H.card : ℝ) + Real.log (1 / δ) ≤ ε * m) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (A m S) ≤ ε}).toReal := by sorry

end FoundationsML.PAC
