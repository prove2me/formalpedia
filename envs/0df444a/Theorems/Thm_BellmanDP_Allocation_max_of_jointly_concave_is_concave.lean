-- Prove2me | Theorems.Thm_BellmanDP_Allocation_max_of_jointly_concave_is_concave
-- name    : BellmanDP.Allocation.max_of_jointly_concave_is_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T05:28:16.603219+00:00
-- url     : https://prove2.me/theorems/b96b11d3-1057-41e2-a4c2-0710477a03f4
-- title:
--   Chapter I, Lemma 1 — maximizing a jointly concave $G(x,y)$ over $0\le y\le x$ gives a concave function
-- statement:
--   Let $G(x,y)$ be concave jointly in $(x,y)$ on the quadrant $x, y \ge 0$, i.e. for $0 \le \lambda \le 1$,
--   $$G\big(\lambda x_1 + (1-\lambda)x_2,\ \lambda y_1 + (1-\lambda)y_2\big) \ge \lambda G(x_1,y_1) + (1-\lambda) G(x_2,y_2).$$
--   Suppose that for every $x \ge 0$ the maximum
--   $$f(x) = \max_{0 \le y \le x} G(x,y)$$
--   is attained. Then $f$ is concave on $[0,\infty)$.
--
--   This lemma is the device by which concavity of the returns $g,h$ is transferred through each stage of the recurrence to the solution of the allocation equation (Theorem 5).
--
--   **Formalization Note** "$f(x)$ as defined by Max" is encoded by requiring, for every $x\ge 0$, that $f(x)$ be the greatest element of $\{G(x,y) : 0\le y\le x\}$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, Lemma 1 and footnote 4, p. 21

import Mathlib

namespace BellmanDP.Allocation

/-- Ch. I, Lemma 1, p. 21. If `G(x, y)` is concave jointly in `(x, y)` on `x, y ≥ 0` and
`f(x) = Max_{0 ≤ y ≤ x} G(x, y)` (the maximum being attained for every `x ≥ 0`), then `f` is
concave on `x ≥ 0`. -/
theorem max_of_jointly_concave_is_concave (G : ℝ → ℝ → ℝ)
    (hG : ConcaveOn ℝ (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) (fun p : ℝ × ℝ => G p.1 p.2))
    (f : ℝ → ℝ) (hf : ∀ x : ℝ, 0 ≤ x → IsGreatest ((G x) '' Set.Icc 0 x) (f x)) :
    ConcaveOn ℝ (Set.Ici 0) f := by sorry

end BellmanDP.Allocation
