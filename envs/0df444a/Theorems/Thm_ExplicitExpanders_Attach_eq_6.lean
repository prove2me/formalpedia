-- Prove2me | Theorems.Thm_ExplicitExpanders_Attach_eq_6
-- name    : ExplicitExpanders.Attach.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:37:56.898833+00:00
-- url     : https://prove2.me/theorems/04d2eef5-c21e-4aaa-9ade-68ff6e34c8b9
-- title:
--   Inequality (6): the combined bound on $|f^tA_Gf|$ for every $x>0$, with the $o(1)$ explicit (Section 2.4)
-- statement:
--   Let $p\ge 0$ and $m\ge1$, let $H$ be a $(p+1)$-regular simple graph on a vertex set $V$ of $m$ vertices whose nontrivial eigenvalues all have absolute value at most $2\sqrt p$, let $R=\{u_1,\dots,u_r\}$ be $r$ new vertices, and let $W_1,\dots,W_r\subseteq V$ be pairwise disjoint sets of exactly $p+2$ vertices each, with $W=\bigcup_iW_i$ and $L=V\setminus W$. Let $A_G=A_H+A_R+A_L$ be the adjacency matrix of the graph $G$ obtained by joining $u_i$ to every vertex of $W_i$ and adding one loop at every vertex of $L$. Then for every real function $f$ on $U=V\cup R$ with $\sum_{u\in U}f(u)=0$ and every real $x>0$,
--   $$|f^{t}A_Gf|\le(2\sqrt p+1)\sum_{v\in L}f^2(v)+(2\sqrt p+x)\sum_{v\in W}f^2(v)+\frac{p+2}{x}\sum_{v\in R}f^2(v)+(p+1)\frac rm\sum_{v\in R}f^2(v).$$
--
--   The paper writes the last term as $o(1)$ (for unit $f$); its proof bounds it by $b^2(p+1)$ from (3), and the Cauchy–Schwarz display gives $b^2\le \frac rm\sum_{v\in R}f^2(v)$, which is the explicit term used here. It tends to $0$ because $r=n-m=o(m)$ by the distribution of primes in progressions (p. 8). Inequality (6) combines (2), (3), (4) and (5), and the bound of Theorem 1.2 follows from it by choosing $x$.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 9, Section 2.4, eq. (6)

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
import Definitions.Def_ExplicitExpanders_Attach_attachMatrix

namespace ExplicitExpanders.Attach

open Matrix

/-- Inequality (6) (arXiv:2003.11673v1, §2.4, p. 9), with the paper's `o(1)` made explicit as
`(p+1) (r/m) ∑_{u∈R} f(u)²`: let `H` be a `(p+1)`-regular graph on `m` vertices whose
nontrivial eigenvalues have absolute value at most `2√p`, let `W i` (`i < r`) be pairwise
disjoint sets of `p + 2` vertices, and let `A_G` be the adjacency matrix of the graph `G`.
For every real `f` on `V ⊕ Fin r` with `∑ f = 0` and every `x > 0`,
`|fᵗ A_G f| ≤ (2√p + 1) ∑_{L} f² + (2√p + x) ∑_{W} f² + (p+2)/x ∑_{R} f² + (p+1)(r/m) ∑_{R} f²`. -/
theorem eq_6 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (p m r : ℕ) (hH : IsNDLambda H m (p + 1) (2 * Real.sqrt p))
    (W : Fin r → Finset V) (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (hcard : ∀ i, (W i).card = p + 2) (f : V ⊕ Fin r → ℝ) (hf : ∑ u, f u = 0)
    (x : ℝ) (hx : 0 < x) :
    |f ⬝ᵥ (matG H W *ᵥ f)| ≤
      (2 * Real.sqrt p + 1) * ∑ v ∈ loopSet W, f (Sum.inl v) ^ 2 +
        (2 * Real.sqrt p + x) * ∑ v ∈ attachedSet W, f (Sum.inl v) ^ 2 +
        ((p : ℝ) + 2) / x * ∑ i, f (Sum.inr i) ^ 2 +
        ((p : ℝ) + 1) * r / m * ∑ i, f (Sum.inr i) ^ 2 := by sorry

end ExplicitExpanders.Attach
