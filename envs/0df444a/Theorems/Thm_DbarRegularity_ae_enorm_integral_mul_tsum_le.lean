-- Prove2me | Theorems.Thm_DbarRegularity_ae_enorm_integral_mul_tsum_le
-- name    : DbarRegularity.ae_enorm_integral_mul_tsum_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:43:23.200176+00:00
-- url     : https://prove2.me/theorems/7ca07681-2f3f-4fbb-863b-0791596abd2d
-- title:
--   Convolution with an $L^2$ kernel of a sum of disjointly supported $L^1$ functions is a.e. bounded by the sum of the convolutions
-- statement:
--   Let $d\ge0$ and $K\in L^2(\mathbb R^d)$, complex valued. Let $(b_k)_{k\in I}$ be a countable family of integrable functions $\mathbb R^d\to\mathbb C$ with pairwise disjoint supports (no point has $b_k(x)\ne0$ and $b_l(x)\ne0$ with $k\ne l$), and suppose $\sum_kb_k$ is integrable. Then for almost every $x\in\mathbb R^d$
--   $$\Big|\int K(x-y)\sum_kb_k(y)\,dy\Big|\;\le\;\sum_k\Big|\int K(x-y)\,b_k(y)\,dy\Big| .$$
--
--   This controls convolution with an $L^2$ kernel applied to the bad part of a Calderón–Zygmund splitting by the sum of its actions on the individual pieces.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`. The index type `ι : Type` is `Countable`, and $\sum_k$ is `tsum`. The inequality is between extended nonnegative reals (`‖·‖ₑ`, with the right side a `tsum` in `ℝ≥0∞`). The integrals are Bochner integrals, which are $0$ where the integrand is not integrable.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, pp. 29–31

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- For `K ∈ L²(ℝ^d)` and integrable functions `bₖ` with pairwise disjoint supports and integrable
sum, almost everywhere `|K * ∑ₖ bₖ| ≤ ∑ₖ |K * bₖ|`. -/
theorem ae_enorm_integral_mul_tsum_le {d : ℕ} {K : EuclideanSpace ℝ (Fin d) → ℂ}
    (hK : MemLp K 2 volume) {ι : Type} [Countable ι] (b : ι → EuclideanSpace ℝ (Fin d) → ℂ)
    (hb : ∀ k, Integrable (b k) volume) (hdisj : ∀ x k l, b k x ≠ 0 → b l x ≠ 0 → k = l)
    (hB : Integrable (fun x => ∑' k, b k x) volume) :
    ∀ᵐ x, ‖∫ y, K (x - y) * ∑' k, b k y‖ₑ ≤ ∑' k, ‖∫ y, K (x - y) * b k y‖ₑ := by sorry

end DbarRegularity
