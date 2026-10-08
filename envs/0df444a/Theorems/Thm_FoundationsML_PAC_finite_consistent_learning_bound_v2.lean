-- Prove2me | Theorems.Thm_FoundationsML_PAC_finite_consistent_learning_bound_v2
-- name    : FoundationsML.PAC.finite_consistent_learning_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:23.251976+00:00
-- url     : https://prove2.me/theorems/552f65b3-3e3d-4731-81b3-9cf4a1c28f1d
-- title:
--   Theorem 2.5 — learning bound, finite $H$, consistent case (measurable error events)
-- statement:
--   **Statement (Theorem 2.5, p. 15, PDF p. 32).** Let $H$ be a finite set of functions mapping from $X$ to $Y$. Let $A$ be an algorithm that, for the target concept $c\in H$ and any i.i.d. sample $S$, returns a consistent hypothesis $h_S\in H$: $\hat R_S(h_S)=0$. Then, for any $\epsilon>0$ and $\delta\in(0,1)$, the inequality $\Pr_{S\sim D^m}[R(h_S)\le\epsilon]\ge1-\delta$ holds for every sample size $m\ge1$ with
--   $$m \ge \frac1\epsilon\Big(\log|H| + \log\frac1\delta\Big).$$
--
--   **Formalization Note.** The retired version stated the book's measurability convention as `Measurable c` and `Measurable h` for an arbitrary σ-algebra on $Y$, which does not make the error events $\{x : h(x)\neq c(x)\}$ measurable (with the trivial σ-algebra on $Y$ every map is measurable, $R(\cdot)$ becomes an outer measure and the union bound fails; this was the accepted disproof). The book's footnote 2 (p. 10), "the family of functions $H$ and the target concept $c$ must be measurable", is now stated as what it is used for: each disagreement set $\{x\mid h(x)\neq c(x)\}$, $h\in H$, is a measurable subset of $X$; no σ-algebra on $Y$ is needed. Also made explicit: $m\ge1$ and $\delta\in(0,1)$ (standing conventions). $A$ is modeled as `∀ m, (Fin m → X) → (X → Y)` with `A m S ∈ H` and `EmpiricalError S c (A m S) = 0`; the sample-complexity condition is written in the multiplied-out form $\log|H|+\log(1/\delta)\le\epsilon m$.
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

**Formalization Note.** Replaces `finite_consistent_learning_bound`, whose measurability
hypotheses (`Measurable c`, `Measurable h` for an arbitrary σ-algebra on `Y`) did not make
the error events `{x | h x ≠ c x}` measurable, so `GeneralizationError` could be an outer
measure and the union bound failed (disproved with the trivial σ-algebra on `Y`). The book's
standing assumption (Definition 2.1, footnote 2, p. 10: "the family of functions `H` and the
target concept `c` must be measurable") is now stated as what it is used for: each
disagreement event `{x | h x ≠ c x}`, `h ∈ H`, is a measurable set. Also `m ≥ 1` and
`δ ∈ (0,1)`, the book's standing conventions. The sample-complexity condition is stated in the
multiplied-out form `log|H| + log(1/δ) ≤ ε·m`. -/
theorem finite_consistent_learning_bound_v2
    {X Y : Type*} [MeasurableSpace X] (H : Finset (X → Y)) (D : Measure X)
    [IsProbabilityMeasure D] (c : X → Y) (hc : c ∈ H)
    (hH_meas : ∀ h ∈ H, MeasurableSet {x | h x ≠ c x})
    (A : ∀ m : ℕ, (Fin m → X) → (X → Y))
    (hA_mem : ∀ m (S : Fin m → X), A m S ∈ H)
    (hA_consistent : ∀ m (S : Fin m → X), EmpiricalError S c (A m S) = 0)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (m : ℕ) (hm0 : 0 < m) (hm : Real.log (H.card : ℝ) + Real.log (1 / δ) ≤ ε * m) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c (A m S) ≤ ε}).toReal := by sorry

end FoundationsML.PAC
