-- Prove2me | Theorems.Thm_FeinbergLiang_ACOE_liminf_eq_liminf_nhds_of_equicontinuous
-- name    : FeinbergLiang.ACOE.liminf_eq_liminf_nhds_of_equicontinuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:01:56.181976+00:00
-- url     : https://prove2.me/theorems/af589613-c65d-4ce2-9aae-a65df458b983
-- title:
--   Lemma 3.3 — for an equicontinuous, pointwise bounded family of nonnegative functions, $\liminf_n f_n(x) = \liminf_{n\to\infty,\,y\to x} f_n(y)$
-- statement:
--   Let $X$ be a metric space and let $\{f_n\}_{n\ge1}$ be a family of nonnegative real-valued functions on $X$. Suppose the family is equicontinuous on $X$ and $\sup_n f_n(x)<\infty$ for each $x\in X$. Then for every $x\in X$,
--   $$\liminf_{n\to\infty}f_n(x)=\tilde f(x):=\liminf_{n\to\infty,\ y\to x}f_n(y).$$
--
--   The joint lower limit on the right is taken as $n\to\infty$ and $y\to x$ simultaneously. The lemma says that, for equicontinuous families, it reduces to the pointwise lower limit. The paper uses it to identify the average-cost relative value function $\tilde u$ with the pointwise limit of the discounted relative value functions.
--
--   **Formalization Note.** Both lower limits are taken in $[0,\infty]$, via `ENNReal.ofReal`, which is exact on nonnegative values. The joint lower limit is along the product filter `atTop ×ˢ 𝓝 x`.
-- source:
--   Feinberg and Liang, On the optimality equation for average cost Markov decision processes and its validity for inventory control, Annals of Operations Research 317, 2022, p. 574, Lemma 3.3, Eq. (3.4)

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

/-- Lemma 3.3 (Feinberg–Liang 2022, p. 574). For an equicontinuous family of nonnegative real
functions `f n` on a metric space with `sup_n f n x < ∞` for each `x`,
`liminf_{n → ∞} f n x = liminf_{n → ∞, y → x} f n y`. Both sides are taken in `ℝ≥0∞`
(`ENNReal.ofReal` is exact on the nonnegative values). -/
theorem liminf_eq_liminf_nhds_of_equicontinuous {Y : Type*} [MetricSpace Y] (f : ℕ → Y → ℝ)
    (hf_nonneg : ∀ n y, 0 ≤ f n y) (hf_equi : Equicontinuous f)
    (hf_bdd : ∀ y, BddAbove (Set.range fun n => f n y)) (x : Y) :
    liminf (fun n => ENNReal.ofReal (f n x)) atTop =
      liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2)) (atTop ×ˢ 𝓝 x) := by sorry

end FeinbergLiang.ACOE
