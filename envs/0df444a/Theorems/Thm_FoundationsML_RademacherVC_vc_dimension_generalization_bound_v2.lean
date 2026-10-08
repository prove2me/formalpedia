-- Prove2me | Theorems.Thm_FoundationsML_RademacherVC_vc_dimension_generalization_bound_v2
-- name    : FoundationsML.RademacherVC.vc_dimension_generalization_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:30.075479+00:00
-- url     : https://prove2.me/theorems/900227be-96c0-4eba-9814-415a4943b7d2
-- title:
--   Corollary 3.19 — VC-dimension generalization bound ($m\ge1$; goal)
-- statement:
--   **Statement (Corollary 3.19, p. 42, PDF p. 59).** Let $H$ be a family of (measurable) functions taking values in $\{-1,+1\}$ with VC-dimension $d$, and $c$ a (measurable) target concept. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample of size $m\ge1$, $m\ge d$, the following holds for all $h\in H$:
--   $$R(h) \le \hat R_S(h) + \sqrt{\frac{2d\log(em/d)}{m}} + \sqrt{\frac{\log(1/\delta)}{2m}}.$$
--
--   **Formalization Note.** The retired version allowed $d=m=0$, where every sample-dependent term is Lean's $x/0=0$ and the bound is false. New statement: $m\ge1$ and $\delta\in(0,1)$ (standing conventions); $d\le m$ kept as the domain of Corollary 3.18 ("for all $m\ge d$") through which the bound is proved; the book's standing measurability (Definition 2.1, footnote 2, p. 10) of $c$ and of every $h\in H$ made explicit (`Bool` carries the discrete σ-algebra, so the error events are measurable). $H$ is `Set (X → Bool)`, `HasVCDim H d` is the chapter's VC-dimension predicate, $em/d$ is `Real.exp 1 * m / d`. For $d=0$ with $m\ge1$ the VC term is Lean's $\sqrt{0}=0$; this is harmless since $\mathrm{VCdim}(H)=0$ forces $H$ to be a single function and the bound reduces to Hoeffding's.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 42, Corollary 3.19 (PDF p. 59)

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_GeneralizationError
import Definitions.Def_FoundationsML_RademacherVC_EmpiricalError
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim

open MeasureTheory

namespace FoundationsML.RademacherVC

/-- Corollary 3.19 (VC-dimension generalization bound; goal; Mohri, Rostamizadeh &
Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 42, PDF p. 59).
Let `H` be a family of functions taking values in `{−1,+1}` (here: `Bool`) with VC-dimension
`d`. Then, for any `δ > 0`, with probability at least `1 − δ` over an i.i.d. sample of size
`m ≥ 1` (`m ≥ d`), the following holds for all `h ∈ H`:
`R(h) ≤ R̂_S(h) + sqrt(2d log(em/d)/m) + sqrt(log(1/δ)/(2m))`.

**Formalization Note.** Replaces `vc_dimension_generalization_bound`, which allowed
`d = m = 0` (every sample-dependent term is then Lean's `x / 0 = 0`). Now `m ≥ 1` and
`δ ∈ (0,1)` (the book's standing conventions); `d ≤ m` is kept as the domain of Corollary 3.18
(`for all m ≥ d`) through which the bound is proved. The book's standing measurability
assumption (Definition 2.1, footnote 2, p. 10) on the target `c` and on every `h ∈ H` is made
explicit (`Bool` carries the discrete σ-algebra, so the error events are then measurable).
`em/d` is `Real.exp 1 * m / d`. -/
theorem vc_dimension_generalization_bound_v2
    {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (H : Set (X → Bool)) (d : ℕ) (hH : HasVCDim H d) (hH_meas : ∀ h ∈ H, Measurable h)
    (c : X → Bool) (hc_meas : Measurable c)
    (m : ℕ) (hm0 : 0 < m) (hm : d ≤ m) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ H, GeneralizationError D c h ≤
        EmpiricalError S c h +
          Real.sqrt (2 * d * Real.log (Real.exp 1 * m / d) / m) +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.RademacherVC
