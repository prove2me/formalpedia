-- Prove2me | Theorems.Thm_DbarRegularity_exists_good_bad_decomposition
-- name    : DbarRegularity.exists_good_bad_decomposition
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:40:21.007769+00:00
-- url     : https://prove2.me/theorems/f99ec650-df72-42d7-bf30-b1ccadd94240
-- title:
--   Calderón–Zygmund good/bad splitting of an integrable function on $\mathbb R^d$ at height $\alpha$
-- statement:
--   Let $d\ge1$. There is a constant $C<\infty$, depending only on $d$, with the following property. For every integrable $f:\mathbb R^d\to\mathbb C$ and every $\alpha>0$ there are a countable index set $I$, centres $c_k\in\mathbb R^d$, radii $r_k\in\mathbb R$ and functions $b_k:\mathbb R^d\to\mathbb C$ ($k\in I$) such that:
--
--   1. each $b_k$ is integrable with $\int b_k=0$, and $b_k$ vanishes outside the closed ball $\bar B(c_k,r_k)$;
--   2. the $b_k$ have pairwise disjoint supports: no point has $b_k(x)\ne0$ and $b_l(x)\ne0$ with $k\ne l$;
--   3. $b=\sum_k b_k$ is integrable, and the good part $g=f-b$ satisfies $|g|\le2^d\alpha$ a.e. and $\|g\|_{L^1}\le\|f\|_{L^1}$;
--   4. $\sum_k\|b_k\|_{L^1}\le2\|f\|_{L^1}$;
--   5. $\sum_k|B(c_k,2r_k)|\le\dfrac{C}{\alpha}\,\|f\|_{L^1}$.
--
--   This is the Calderón–Zygmund splitting $f=g+\sum_k b_k$ at height $\alpha$ in the form used for weak-type $(1,1)$ estimates of singular integrals: a bounded good part, plus mean-zero bad pieces localized in balls whose doubles have total measure $O(\|f\|_1/\alpha)$.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`, and $d\ge1$ is `0 < d`. The constant is `C : ℝ≥0∞` with `C ≠ ⊤`. The index type `ι : Type` is `Countable`, and $\sum_k b_k(x)$ is the pointwise `tsum` `∑' k, b k x`. $L^1$ norms are `eLpNorm · 1 volume`. Item 5 is `∑' k, volume (ball (c k) (2 * r k)) ≤ C / ENNReal.ofReal α * eLpNorm f 1 volume`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, pp. 29–31

import Definitions.Def_DbarRegularity_Setting
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal

/-- Calderón–Zygmund good/bad splitting of an integrable `f : ℝ^d → ℂ` at height `α`:
`f = g + ∑ₖ bₖ` with `|g| ≤ 2^d α` a.e., `‖g‖₁ ≤ ‖f‖₁`, and mean-zero pieces `bₖ` with disjoint
supports in balls `B̄(cₖ, rₖ)` such that `∑ ‖bₖ‖₁ ≤ 2 ‖f‖₁` and `∑ |B(cₖ, 2rₖ)| ≤ (C / α) ‖f‖₁`. -/
theorem exists_good_bad_decomposition {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f : EuclideanSpace ℝ (Fin d) → ℂ), Integrable f volume →
      ∀ α : ℝ, 0 < α →
      ∃ (ι : Type) (_ : Countable ι) (c : ι → EuclideanSpace ℝ (Fin d)) (r : ι → ℝ)
        (b : ι → EuclideanSpace ℝ (Fin d) → ℂ),
        (∀ k, Integrable (b k) volume) ∧
        (∀ k, ∫ x, b k x = 0) ∧
        (∀ k x, b k x ≠ 0 → x ∈ closedBall (c k) (r k)) ∧
        (∀ x k l, b k x ≠ 0 → b l x ≠ 0 → k = l) ∧
        Integrable (fun x => ∑' k, b k x) volume ∧
        (∀ᵐ x, ‖f x - ∑' k, b k x‖ ≤ 2 ^ d * α) ∧
        eLpNorm (fun x => f x - ∑' k, b k x) 1 volume ≤ eLpNorm f 1 volume ∧
        ∑' k, eLpNorm (b k) 1 volume ≤ 2 * eLpNorm f 1 volume ∧
        ∑' k, volume (ball (c k) (2 * r k)) ≤ C / ENNReal.ofReal α * eLpNorm f 1 volume := by sorry

end DbarRegularity
