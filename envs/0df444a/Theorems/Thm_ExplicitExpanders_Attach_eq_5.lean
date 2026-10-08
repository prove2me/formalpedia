-- Prove2me | Theorems.Thm_ExplicitExpanders_Attach_eq_5
-- name    : ExplicitExpanders.Attach.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:37:38.029174+00:00
-- url     : https://prove2.me/theorems/c7e10efe-3676-434b-93ca-397cac46ff02
-- title:
--   Inequality (5): $|f^tA_Rf|\le\frac{p+2}{x}\sum_Rf^2+x\sum_Wf^2$ for every $x>0$ (Section 2.4)
-- statement:
--   Let $V$ be a finite set, $p\ge 0$, and $R=\{u_1,\dots,u_r\}$ a set of $r$ new vertices. Let $W_1,\dots,W_r\subseteq V$ be pairwise disjoint sets, each of exactly $p+2$ elements, and $W=\bigcup_iW_i$. Let $A_R$ be the adjacency matrix on $U=V\cup R$ of the union $E_R$ of the stars joining $u_i$ to the vertices of $W_i$. Then for every real function $f$ on $U$ and every real $x>0$,
--   $$f^tA_Rf=2\sum_{i=1}^r\sum_{v\in W_i}f(u_i)f(v)=2\sum_{uv\in E_R}f(u)f(v),$$
--   and
--   $$|f^{t}A_Rf|\le\frac{p+2}{x}\sum_{u\in R}f^2(u)+x\sum_{v\in W}f^2(v).$$
--
--   This bounds the part of $f^tA_Gf$ contributed by the edges to the new vertices in the proof of Theorem 1.2. The free parameter $x$ is chosen later to balance this bound against the bounds for the other two parts.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 9, Section 2.4, eq. (5); W and E_R defined on p. 8

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
import Definitions.Def_ExplicitExpanders_Attach_attachMatrix

namespace ExplicitExpanders.Attach

open Matrix

/-- Inequality (5) (arXiv:2003.11673v1, §2.4, p. 9): if the sets `W i` (`i < r`) are pairwise
disjoint and each has `p + 2` elements, then for every real `f` on `V ⊕ Fin r` and every
`x > 0`, `fᵗ A_R f = 2 ∑_{uv ∈ E_R} f(u) f(v)` and
`|fᵗ A_R f| ≤ (p+2)/x ∑_{u∈R} f(u)² + x ∑_{v∈W} f(v)²`, where `W = ⋃ᵢ W i`. -/
theorem eq_5 {V : Type*} [Fintype V] [DecidableEq V] (p r : ℕ) (W : Fin r → Finset V)
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j)) (hcard : ∀ i, (W i).card = p + 2)
    (f : V ⊕ Fin r → ℝ) (x : ℝ) (hx : 0 < x) :
    f ⬝ᵥ (matR W *ᵥ f) = 2 * ∑ i, ∑ v ∈ W i, f (Sum.inr i) * f (Sum.inl v) ∧
      |f ⬝ᵥ (matR W *ᵥ f)| ≤
        ((p : ℝ) + 2) / x * ∑ i, f (Sum.inr i) ^ 2 +
          x * ∑ v ∈ attachedSet W, f (Sum.inl v) ^ 2 := by sorry

end ExplicitExpanders.Attach
