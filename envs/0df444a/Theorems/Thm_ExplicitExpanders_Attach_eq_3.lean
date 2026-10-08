-- Prove2me | Theorems.Thm_ExplicitExpanders_Attach_eq_3
-- name    : ExplicitExpanders.Attach.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T06:37:16.572811+00:00
-- url     : https://prove2.me/theorems/c6a30789-a7fb-40fc-a57a-059ec4c1dc70
-- title:
--   Inequality (3): $|f^tA_Hf|\le b^2(p+1)+c^2\,2\sqrt p$ for a $(p+1)$-regular Ramanujan graph $H$ (Section 2.4)
-- statement:
--   Let $p\ge 0$ and $m\ge 1$ be integers, and let $H$ be a $(p+1)$-regular simple graph on a vertex set $V$ of $m$ vertices whose nontrivial eigenvalues all have absolute value at most $2\sqrt p$ (an $(m,p+1,2\sqrt p)$-graph). Let $R$ be a set of $r$ new vertices and let $A_H$ be the adjacency matrix of $H$ extended by zero to $U=V\cup R$. For a real function $f$ on $U$ put
--   $$b^2=\frac{\big(\sum_{v\in V}f(v)\big)^2}{m},\qquad c^2=\sum_{v\in V}f^2(v)-b^2 .$$
--   Then
--   $$|f^{t}A_Hf|\le b^2(p+1)+c^2\,2\sqrt p .$$
--
--   Here $b^2$ and $c^2$ are the squared lengths of the components of the restriction $f'$ of $f$ to $V$ along the normalised constant vector $g=\mathbf 1/\sqrt m$ and orthogonal to it. This is the bound on the $H$-part of $f^tA_Gf$ in the proof of Theorem 1.2; combined with the Cauchy–Schwarz display, $b^2\le r/m$ for a unit vector $f$ orthogonal to the constant vector on $U$, and the paper concludes $|f^tA_Hf|\le 2\sqrt p+o(1)$.
--
--   **Formalization Note** The paper writes $b^2+c^2=1$; since $f'$ is the restriction of a unit vector it is not itself a unit vector, and the correct relation, used here, is $b^2+c^2=\sum_{v\in V}f^2(v)\le 1$. The bound then reads as above. The hypothesis on $H$ is the spectral property supplied by the Lubotzky–Phillips–Sarnak construction; $H$ itself is arbitrary.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 9, Section 2.4, eq. (3)

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
import Definitions.Def_ExplicitExpanders_Attach_attachMatrix

namespace ExplicitExpanders.Attach

open Matrix

/-- Inequality (3) (arXiv:2003.11673v1, §2.4, p. 9), with the paper's `b² + c² = 1` corrected
to `b² + c² = ∑_{v∈V} f(v)²`: let `H` be a `(p+1)`-regular graph on `m` vertices whose
nontrivial eigenvalues have absolute value at most `2√p`, and `A_H` its adjacency matrix
extended by zero to `V ⊕ Fin r`. For every real `f` on `V ⊕ Fin r`, with
`b² = (∑_{v∈V} f(v))² / m` and `c² = ∑_{v∈V} f(v)² - b²`,
`|fᵗ A_H f| ≤ b² (p + 1) + c² · 2√p`. -/
theorem eq_3 {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (H : SimpleGraph V)
    [DecidableRel H.Adj] (p m r : ℕ) (hH : IsNDLambda H m (p + 1) (2 * Real.sqrt p))
    (f : V ⊕ Fin r → ℝ) :
    |f ⬝ᵥ (matH H r *ᵥ f)| ≤
      (∑ v, f (Sum.inl v)) ^ 2 / m * ((p : ℝ) + 1) +
        (∑ v, f (Sum.inl v) ^ 2 - (∑ v, f (Sum.inl v)) ^ 2 / m) * (2 * Real.sqrt p) := by sorry

end ExplicitExpanders.Attach
