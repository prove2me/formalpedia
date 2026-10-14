-- Prove2me | Theorems.Thm_DbarRegularity_maximalFunction_lowerSemicontinuous
-- name    : DbarRegularity.maximalFunction_lowerSemicontinuous
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T22:28:18.434435+00:00
-- url     : https://prove2.me/theorems/16f72ae0-af97-4a32-b038-916b3c253854
-- title:
--   The Hardy–Littlewood maximal function is lower semicontinuous
-- statement:
--   Let $Mf$ be the Hardy–Littlewood maximal function of $f:\mathbb{R}^d\to\mathbb{C}$,
--   $$Mf(x)=\sup_{r>0}\frac{1}{|B(x,r)|}\int_{B(x,r)}|f(y)|\,dy\in[0,\infty],$$
--   where $B(x,r)$ is the open ball and $|\cdot|$ is Lebesgue measure. Then $Mf:\mathbb{R}^d\to[0,\infty]$ is lower semicontinuous: for every $x$ and every $\alpha<Mf(x)$ there is a neighbourhood $U$ of $x$ with $\alpha<Mf(x')$ for all $x'\in U$.
--
--   Equivalently, every superlevel set $\{Mf>\alpha\}$ is open. In particular $Mf$ is Borel measurable, so its $L^p$ norms and distribution function are meaningful for every $f$.
--
--   **Formalization Note.** `maximalFunction f` (from `Definitions.Def_DbarRegularity_Setting`) takes values in `ℝ≥0∞`, and lower semicontinuity is Mathlib's `LowerSemicontinuous`. No measurability or integrability is assumed on $f$ (the integrals are lower Lebesgue integrals `∫⁻`). The case $d=0$ is included.
-- source:
--   Auxiliary statement for E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 1.3, Theorem 1, p. 5 (measurability of the maximal function)

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Topology.Semicontinuity.Basic

namespace DbarRegularity

open MeasureTheory

/-- The Hardy–Littlewood maximal function `M f` of any `f : ℝ^d → ℂ` is lower semicontinuous as a
`[0, ∞]`-valued function. -/
theorem maximalFunction_lowerSemicontinuous (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) :
    LowerSemicontinuous (maximalFunction f) := by sorry

end DbarRegularity
