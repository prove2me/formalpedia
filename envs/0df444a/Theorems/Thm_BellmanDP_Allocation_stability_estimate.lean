-- Prove2me | Theorems.Thm_BellmanDP_Allocation_stability_estimate
-- name    : BellmanDP.Allocation.stability_estimate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:13:50.109507+00:00
-- url     : https://prove2.me/theorems/9f2bcb7b-645a-41fe-b95e-74712a2275df
-- title:
--   Chapter I, Theorem 9 — stability: $|f(x)-F(x)|\le\sum_{n\ge0}D(c^nx)$
-- statement:
--   Let $u(x,y)$ and $v(x,y)$ be continuous for $x,y\ge 0$, let $0<a<1$, $0<b<1$ and $c=\max(a,b)$. Put
--   $$m(z) = \max_{0\le x\le z}\,\max_{0\le y\le x}\max\big(|u(x,y)|,|v(x,y)|\big), \qquad D(z) = \max_{0\le x\le z}\,\max_{0\le y\le x}|u(x,y)-v(x,y)|,$$
--   and assume $\sum_{n\ge 0} m(c^n z)<\infty$ and $\sum_{n\ge0} D(c^n z) < \infty$ for all $z\ge 0$. Let $f$ and $F$ be continuous on $[0,\infty)$ with $f(0)=F(0)=0$ and solve
--   $$f(x) = \max_{0\le y\le x}\big[u(x,y) + f(ay+b(x-y))\big], \qquad F(x) = \max_{0\le y\le x}\big[v(x,y) + F(ay+b(x-y))\big]$$
--   for $x \ge 0$. Then for every $x\ge 0$,
--   $$|f(x)-F(x)| \le \sum_{n=0}^{\infty} D(c^n x).$$
--
--   The estimate justifies replacing a return function by a simpler approximation (a monomial or a quadratic) and bounds the resulting error in the value.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 18, Eq. (18.1) and Theorem 9, p. 29

import Mathlib
import Definitions.Def_BellmanDP_Allocation_GeneralEquation

namespace BellmanDP.Allocation

/-- Ch. I, Theorem 9, p. 29. Let `u, v` be continuous on `x, y ≥ 0`, `0 < a, b < 1`,
`c = Max(a, b)`, `m(z) = Max_{0 ≤ x ≤ z} Max_{0 ≤ y ≤ x} Max(|u(x, y)|, |v(x, y)|)` with
`Σ m(cⁿ z) < ∞`, and `D(z) = Max_{0 ≤ x ≤ z} Max_{0 ≤ y ≤ x} |u(x, y) − v(x, y)|` with
`Σ D(cⁿ z) < ∞`, for all `z ≥ 0`. If `f` and `F` are continuous solutions on `x ≥ 0`, vanishing at
`0`, of `f(x) = Max_{0 ≤ y ≤ x} [u(x, y) + f(ay + b(x − y))]` and of the same equation with `v`,
then `|f(x) − F(x)| ≤ Σ_{n=0}^∞ D(cⁿ x)` for all `x ≥ 0`. -/
theorem stability_estimate (u v : ℝ → ℝ → ℝ) (a b : ℝ)
    (ha0 : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb1 : b < 1)
    (hu : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
    (hv : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)))
    (hm : ∀ z : ℝ, 0 ≤ z → Summable (fun n : ℕ =>
      triangleMax (fun s t => max |u s t| |v s t|) (max a b ^ n * z)))
    (hD : ∀ z : ℝ, 0 ≤ z → Summable (fun n : ℕ =>
      triangleMax (fun s t => |u s t - v s t|) (max a b ^ n * z)))
    (f F : ℝ → ℝ)
    (hfc : ContinuousOn f (Set.Ici 0)) (hf0 : f 0 = 0) (hf : IsGeneralSolution u a b f)
    (hFc : ContinuousOn F (Set.Ici 0)) (hF0 : F 0 = 0) (hF : IsGeneralSolution v a b F) :
    ∀ x : ℝ, 0 ≤ x →
      |f x - F x| ≤ ∑' n : ℕ, triangleMax (fun s t => |u s t - v s t|) (max a b ^ n * x) := by sorry

end BellmanDP.Allocation
