-- Prove2me | Theorems.Thm_FoundationsML_MultiClass_margin_bound_kernel_multiclass_v2
-- name    : FoundationsML.MultiClass.margin_bound_kernel_multiclass_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:18:13.528975+00:00
-- url     : https://prove2.me/theorems/9a663432-3496-47df-9de0-421073be8e17
-- title:
--   Corollary 9.4 — margin bound for kernel-based multi-class hypotheses (corrected margin, $m\ge1$)
-- statement:
--   **Statement (Corollary 9.4, p. 220, PDF p. 237).** Let $K$ be a PDS kernel with feature map $\Phi$ and $K(x,x)\le r^2$ for all $x$, $H_{K,p}=\{(x,y)\mapsto w_y\cdot\Phi(x):\|W\|_{H,p}\le\Lambda\}$ with $p\ge1$, and $f$ a (measurable) target with $k\ge2$ classes. Fix $\rho>0$. Then, for any $\delta\in(0,1)$, with probability at least $1-\delta$ over an i.i.d. sample of size $m\ge1$, for all $h\in H_{K,p}$:
--   $$R(h) \le \hat R_{S,\rho}(h) + 4k\sqrt{\frac{r^2\Lambda^2/\rho^2}{m}} + \sqrt{\frac{\log(1/\delta)}{2m}}.$$
--
--   **Formalization Note.** The retired version allowed $m=0$ (every sample-dependent term is Lean's $x/0=0$). Changes: $m\ge1$, $\delta\in(0,1)$; the margin, risk and empirical margin loss are the corrected `MarginFunction`/`GeneralizationError`/`EmpiricalMarginLoss` (`_v2`, maximum over exactly the labels $y'\ne y$); the book's standing measurability (footnote 2, p. 10) of $f$ and of the kernel hypotheses $x\mapsto\langle w,\Phi(x)\rangle$ is explicit. The remaining hypotheses are Proposition 9.3's.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 220, Corollary 9.4 (PDF p. 237)

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_GeneralizationError_v2
import Definitions.Def_FoundationsML_MultiClass_EmpiricalMarginLoss_v2
import Definitions.Def_FoundationsML_MultiClass_IsPDS
import Definitions.Def_FoundationsML_MultiClass_KernelHypothesisClass

open MeasureTheory

namespace FoundationsML.MultiClass

/-- Corollary 9.4 (Margin bound for multi-class classification with kernel-based hypotheses;
Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
p. 220, PDF p. 237). Let `K` be a PDS kernel with feature map `Φ` and `K(x,x) ≤ r²` for all
`x`, `H_{K,p} = {(x,y) ↦ w_y·Φ(x) : ‖W‖_{H,p} ≤ Λ}`, fix `ρ > 0`. Then, for any `δ > 0`, with
probability at least `1 − δ` over an i.i.d. sample of size `m ≥ 1`, the following holds for
all `h ∈ H_{K,p}`: `R(h) ≤ R̂_{S,ρ}(h) + 4k sqrt(r²Λ²/ρ²/m) + sqrt(log(1/δ)/(2m))`.

**Formalization Note.** Replaces `margin_bound_kernel_multiclass`, which allowed `m = 0`
(every sample-dependent term is then Lean's `x / 0 = 0`). Changes: `m ≥ 1`, `δ ∈ (0,1)`
(standing conventions); the margin, risk and empirical margin loss are the corrected
`MarginFunction`/`GeneralizationError`/`EmpiricalMarginLoss` (`_v2`, maximum over exactly the
labels `y' ≠ y`); the book's standing measurability (footnote 2, p. 10) of the target `f` and
of the kernel hypotheses `x ↦ ⟪w, Φ(x)⟫` is explicit. The remaining hypotheses are
Proposition 9.3's (`K` PDS with feature map `Φ`, `K(x,x) ≤ r²`, `p ≥ 1`, `Λ > 0`, `k ≥ 2`
classes). -/
theorem margin_bound_kernel_multiclass_v2
    {X Hb : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    [NormedAddCommGroup Hb] [InnerProductSpace ℝ Hb]
    (K : X → X → ℝ) (Φ : X → Hb) (hK : IsPDS K)
    (hΦ : ∀ x y, K x y = (inner (𝕜 := ℝ) (Φ x) (Φ y) : ℝ))
    (hΦmeas : ∀ w : Hb, Measurable (fun x => (inner (𝕜 := ℝ) w (Φ x) : ℝ)))
    (r : ℝ) (hr : 0 < r) (hrK : ∀ x, K x x ≤ r ^ 2)
    (k : ℕ) (hk2 : 2 ≤ k) (p Λ : ℝ) (hp : 1 ≤ p) (hΛ : 0 < Λ)
    (f : X → Fin k) (hf : Measurable f) (m : ℕ) (hm : 0 < m)
    (ρ : ℝ) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ h ∈ KernelHypothesisClass Φ k p Λ, GeneralizationError D f h ≤
        EmpiricalMarginLoss ρ S f h + 4 * (k : ℝ) * Real.sqrt (r ^ 2 * Λ ^ 2 / ρ ^ 2 / m) +
          Real.sqrt (Real.log (1 / δ) / (2 * m))}).toReal := by sorry

end FoundationsML.MultiClass
