-- Prove2me | Theorems.Thm_FoundationsML_PAC_single_hypothesis_generalization_bound_v2
-- name    : FoundationsML.PAC.single_hypothesis_generalization_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:19.024981+00:00
-- url     : https://prove2.me/theorems/9a1ef3df-e8d9-4f45-8c25-379b12329c40
-- title:
--   Corollary 2.11 — generalization bound, single hypothesis ($m\ge1$)
-- statement:
--   **Statement (Corollary 2.11, p. 19, PDF p. 36).** Fix a hypothesis $h : X \to \{0,1\}$ and a target concept $c$. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample $S\sim D^m$ of size $m\ge1$,
--   $$R(h) \le \hat R_S(h) + \sqrt{\frac{\log(2/\delta)}{2m}}.$$
--   This is Hoeffding's inequality (Theorem D.2, Corollary 2.10) applied to a single fixed hypothesis.
--
--   **Formalization Note.** The retired version allowed the degenerate sample size $m=0$, where Lean's convention $x/0=0$ turns both $\hat R_S(h)$ and the deviation term into $0$ and the bound is false. The new statement requires $m\ge1$ and $\delta\in(0,1)$, the book's standing conventions for "a sample of size $m$" and a confidence parameter (for $\delta\ge1$ the claim is vacuous). As before, the sample is the identity random variable on $(\mathrm{Fin}\,m\to X,\ D^{\otimes m})$, and the book's standing measurability hypothesis (Definition 2.1, footnote 2, p. 10) on $c$ and $h$ is carried explicitly.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 19, Corollary 2.11 (PDF p. 36)

import Mathlib
import Definitions.Def_FoundationsML_PAC_GeneralizationError
import Definitions.Def_FoundationsML_PAC_EmpiricalError

open MeasureTheory

namespace FoundationsML.PAC

/-- Corollary 2.11 (Generalization bound — single hypothesis; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 19, PDF p. 36).
Fix a hypothesis `h : X → {0,1}` and a target concept `c`. Then, for any `δ > 0`, with
probability at least `1 − δ` over an i.i.d. sample `S ∼ D^m` of size `m ≥ 1`,
`R(h) ≤ R̂_S(h) + sqrt(log(2/δ) / (2m))`.

**Formalization Note.** Replaces `single_hypothesis_generalization_bound`, which allowed the
degenerate sample size `m = 0` (where Lean's `x / 0 = 0` turns both `R̂_S(h)` and the
deviation term into `0`, making the bound false). The sample size is now `m ≥ 1` and the
confidence parameter is `δ ∈ (0,1)`, the book's standing conventions for "a sample of size
`m`" and a confidence level. Carries the book's standing measurability hypothesis
(Definition 2.1, footnote 2, p. 10) on `c` and `h`. -/
theorem single_hypothesis_generalization_bound_v2
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c h : X → Bool) (hc_meas : Measurable c) (hh_meas : Measurable h)
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | GeneralizationError D c h ≤
        EmpiricalError S c h + Real.sqrt (Real.log (2 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.PAC
