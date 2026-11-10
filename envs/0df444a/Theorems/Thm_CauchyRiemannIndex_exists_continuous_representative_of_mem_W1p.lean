-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_continuous_representative_of_mem_W1p
-- name    : CauchyRiemannIndex.exists_continuous_representative_of_mem_W1p
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T16:41:27.935196+00:00
-- url     : https://prove2.me/theorems/abcf43a8-5d0f-4e01-a2d7-427009779ac0
-- title:
--   Continuous bounded representatives of W^{1,p} on the cylinder, p > 2
-- statement:
--   Let $2 < p < \infty$. There is a constant $C$ such that for every $w = (w_1, w_2, w_3) \in W^{1,p}(\mathbb{R}\times S^1, \mathbb{R}^{2n})$ (the stage-5 space `W1p p n`, the closure of test triples $(u, \partial_s u, \partial_t u)$ in $L^p\times L^p\times L^p$ with the product norm):
--
--   1. $w_1$ has a continuous representative $g$, $1$-periodic in $t$, with $w_1 = g$ almost everywhere on the strip;
--   2. every continuous, $t$-periodic $g$ with $w_1 = g$ a.e. satisfies $|g(x)| \le C\,\|w\|$ for all $x$, and $\sup_t |g(s,t)| \to 0$ as $|s| \to \infty$.
--
--   **Role.** Embedding $W^{1,p}(\mathbb{R}\times S^1) \hookrightarrow C^0$ for $p > 2$, used for Nemytskii-type operators on $W^{1,p}$. Because the bound holds for every continuous representative, it also bounds differences: $|g_w(x) - g_{w'}(x)| \le C\|w - w'\|$.
-- source:
--   Standard Sobolev embedding on the cylinder; setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry (arXiv:1011.1690), Ch. 4

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open MeasureTheory
open scoped ENNReal NNReal

/-- For `2 < p < ∞`, the first component of every `w ∈ W^{1,p}(ℝ × S¹)` has a continuous
representative, `1`-periodic in `t`; every such representative is bounded by `C ‖w‖` (with `C`
independent of `w`) and tends to `0` as `|s| → ∞`, uniformly in `t`. -/
theorem exists_continuous_representative_of_mem_W1p (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : 2 < p)
    (hp' : p ≠ ⊤) (n : ℕ) :
    ∃ C : ℝ, ∀ w ∈ W1p p n,
      (∃ g : ℝ × ℝ → Vec n, Continuous g ∧ (∀ s t, g (s, t + 1) = g (s, t)) ∧
        (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g) ∧
      ∀ g : ℝ × ℝ → Vec n, Continuous g → (∀ s t, g (s, t + 1) = g (s, t)) →
        (w.1 : ℝ × ℝ → Vec n) =ᵐ[cylMeasure] g →
        (∀ x, ‖g x‖ ≤ C * ‖w‖) ∧ ∀ ε > 0, ∃ R : ℝ, ∀ s t, R < |s| → ‖g (s, t)‖ < ε := by
  sorry

end CauchyRiemannIndex
