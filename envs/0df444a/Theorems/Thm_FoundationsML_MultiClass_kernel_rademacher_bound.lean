-- Prove2me | Theorems.Thm_FoundationsML_MultiClass_kernel_rademacher_bound
-- name    : FoundationsML.MultiClass.kernel_rademacher_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T23:34:05.80012+00:00
-- url     : https://prove2.me/theorems/d6db13ca-acc6-4fbc-a278-9ddd60dc03c2
-- title:
--   Proposition 9.3 — Rademacher complexity of multi-class kernel-based hypotheses
-- statement:
--   **Statement (Proposition 9.3, p. 219, PDF p. 236).** Let $K$ be a PDS kernel with feature
--   map $\Phi$ ($K(x,y)=\langle\Phi(x),\Phi(y)\rangle$), and assume $K(x,x)\le r^2$ for all $x$.
--   Then, for any $m\ge1$, $R_m(\Pi_1(H_{K,p})) \le \sqrt{r^2\Lambda^2/m}$. Makes Theorem 9.2's
--   bound fully explicit for kernel-based multi-class hypotheses.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 219, Proposition 9.3 (PDF p. 236)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_RademacherComplexity
import Definitions.Def_FoundationsML_MultiClass_EmpiricalRademacherComplexity
import Definitions.Def_FoundationsML_MultiClass_Proj1
import Definitions.Def_FoundationsML_MultiClass_IsPDS
import Definitions.Def_FoundationsML_MultiClass_KernelHypothesisClass

open MeasureTheory

namespace FoundationsML.MultiClass

/-- Proposition 9.3 (Rademacher complexity of multi-class kernel-based hypotheses; Mohri,
Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018, p. 219,
PDF p. 236). Let `K` be a PDS kernel with feature map `Φ` (`K x y = ⟪Φ x, Φ y⟫`), and assume
`K(x,x) ≤ r²` for all `x`. Then, for any `m ≥ 1`, `R_m(Π_1(H_{K,p})) ≤ sqrt(r²Λ²/m)`.

**Formalization Note.** `hInt` guards `RademacherComplexity`'s outer Bochner integral against
trap 2 directly (rather than via a `Measurable Φ` hypothesis, which would need a
`MeasurableSpace Hb` instance this theorem's ambient Hilbert space does not otherwise carry):
without it, a non-measurable `Φ` could junk the integral to `0`, making the conclusion provable
as `0 ≤ Real.sqrt (...)` (always true) without using `hK`, `hΦ`, `hrK`, `hp`, or `hΛ` at all —
the "makes it trivially true" direction of trap 2. The pointwise boundedness the inner `⨆`
needs is already derivable from `hrK`/`hΛ` via the book's own Cauchy-Schwarz argument, so only
the outer integral needs an explicit guard. -/
theorem kernel_rademacher_bound
    {X Hb : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (K : X → X → ℝ) (Φ : X → Hb) (hK : IsPDS K) (hΦ : ∀ x y, K x y = (inner (𝕜 := ℝ) (Φ x) (Φ y) : ℝ))
    (r : ℝ) (hr : 0 < r) (hrK : ∀ x, K x x ≤ r ^ 2)
    (k : ℕ) (hk : 0 < k) (p Λ : ℝ) (hp : 1 ≤ p) (hΛ : 0 < Λ) (m : ℕ) (hm : 0 < m)
    (hInt : Integrable
      (fun S => EmpiricalRademacherComplexity (Proj1 (KernelHypothesisClass Φ k p Λ)) S)
      (Measure.pi fun _ : Fin m => D)) :
    RademacherComplexity D (Proj1 (KernelHypothesisClass Φ k p Λ)) m ≤
      Real.sqrt (r ^ 2 * Λ ^ 2 / m) := by sorry

end FoundationsML.MultiClass
