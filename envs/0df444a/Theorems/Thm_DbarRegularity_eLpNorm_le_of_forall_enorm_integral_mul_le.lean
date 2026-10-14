-- Prove2me | Theorems.Thm_DbarRegularity_eLpNorm_le_of_forall_enorm_integral_mul_le
-- name    : DbarRegularity.eLpNorm_le_of_forall_enorm_integral_mul_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T16:59:32.182863+00:00
-- url     : https://prove2.me/theorems/badaad2b-6c2d-4a8d-b17b-bdf94d329a2c
-- title:
--   $L^p$ norm by duality on $\mathbb R^d$: $|\int hg|\le M\|g\|_{q}$ for all $g\in\bigcap_rL^r$ implies $\|h\|_{p}\le M$
-- statement:
--   Let $d\ge0$, $1<p<\infty$ and $q=p/(p-1)$. Let $h:\mathbb R^d\to\mathbb C$ be a.e.-strongly measurable and $M\in[0,\infty]$. Suppose that
--   $$\Big|\int_{\mathbb R^d}h(x)\,g(x)\,dx\Big|\le M\,\|g\|_{L^q}$$
--   for every $g:\mathbb R^d\to\mathbb C$ that belongs to $L^r(\mathbb R^d)$ for every $r\in[1,\infty]$. Then $\|h\|_{L^p}\le M$.
--
--   In particular $h\in L^p$ whenever $M<\infty$. This is the norm-duality principle $\|h\|_p=\sup\{|\int hg|:\|g\|_q\le1\}$ in the form needed for $L^p$ bounds of operators: only test functions in every $L^r$ have to be checked, and nothing is assumed about $h$ beyond measurability.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. The exponents $p,q$ are real numbers, with `hq : q = p / (p - 1)`, and the norms are `eLpNorm · (ENNReal.ofReal p) volume`. The test class is `∀ r : ℝ≥0∞, 1 ≤ r → MemLp g r volume`. The pairing is the Bochner integral `∫ x, h x * g x` (set to $0$ where not integrable), compared through `‖·‖ₑ` with `M * eLpNorm g (ENNReal.ofReal q) volume`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 31 (duality step)

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- `L^p` norm by testing: if `|∫ h g| ≤ M ‖g‖_q` (with `1/p + 1/q = 1`, `1 < p < ∞`) for every
`g : ℝ^d → ℂ` lying in every `L^r`, `1 ≤ r ≤ ∞`, then `‖h‖_p ≤ M`. -/
theorem eLpNorm_le_of_forall_enorm_integral_mul_le {d : ℕ} {h : EuclideanSpace ℝ (Fin d) → ℂ}
    (hh : AEStronglyMeasurable h volume) {p q : ℝ} (hp : 1 < p) (hq : q = p / (p - 1))
    (M : ℝ≥0∞)
    (H : ∀ g : EuclideanSpace ℝ (Fin d) → ℂ, (∀ r : ℝ≥0∞, 1 ≤ r → MemLp g r volume) →
      ‖∫ x, h x * g x‖ₑ ≤ M * eLpNorm g (ENNReal.ofReal q) volume) :
    eLpNorm h (ENNReal.ofReal p) volume ≤ M := by sorry

end DbarRegularity
