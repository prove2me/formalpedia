-- Prove2me | Theorems.Thm_DbarRegularity_memLp_indicator_le_norm
-- name    : DbarRegularity.memLp_indicator_le_norm
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:36:38.04376+00:00
-- url     : https://prove2.me/theorems/b06bfc57-a1d8-47b4-911d-7653b88a882a
-- title:
--   Truncations of size-|x|^(-d) kernels lie in L^q for q > 1
-- statement:
--   Let $d\ge1$, $B\in\mathbb{R}$, and let $K:\mathbb{R}^d\to\mathbb{C}$ be measurable with $|K(x)|\le B|x|^{-d}$ for $x\neq0$. Then for every $\varepsilon>0$ and every real $q>1$ the truncated kernel $K\,\mathbf 1_{\{|x|\ge\varepsilon\}}$ belongs to $L^q(\mathbb{R}^d)$.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`; measurability is `AEStronglyMeasurable K volume`; the truncation is `{x | ε ≤ ‖x‖}.indicator K`; the exponent is `ENNReal.ofReal q`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 3.2, p. 35

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- If `|K(x)| ≤ B |x|^{-d}` for `x ≠ 0`, then `K · 1_{|x| ≥ ε}` lies in `L^q(ℝ^d)` for every
`q > 1` and `ε > 0`. -/
theorem memLp_indicator_le_norm {d : ℕ} (hd : 0 < d) (K : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK : AEStronglyMeasurable K volume) (B : ℝ) (hB : ∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d)
    (ε : ℝ) (hε : 0 < ε) (q : ℝ) (hq : 1 < q) :
    MemLp ({x | ε ≤ ‖x‖}.indicator K) (ENNReal.ofReal q) volume := by sorry

end DbarRegularity
