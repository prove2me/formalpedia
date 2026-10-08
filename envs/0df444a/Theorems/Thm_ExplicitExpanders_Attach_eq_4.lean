-- Prove2me | Theorems.Thm_ExplicitExpanders_Attach_eq_4
-- name    : ExplicitExpanders.Attach.eq_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:37:34.483148+00:00
-- url     : https://prove2.me/theorems/2ad495a5-e0df-4cc8-9894-cdf21efa6c6a
-- title:
--   Display (4): $f^tA_Lf=\sum_{v\in L}f^2(v)$ for the loops on $L$ (Section 2.4)
-- statement:
--   Let $V$ be a finite set, $R$ a set of $r$ new vertices, $W_1,\dots,W_r\subseteq V$, $L=V\setminus\bigcup_i W_i$, and let $A_L$ be the diagonal matrix on $U=V\cup R$ with entry $1$ at each vertex of $L$ (one loop there) and $0$ elsewhere. For every real function $f$ on $U$,
--   $$f^{t}A_Lf=\sum_{v\in L}f^2(v).$$
--
--   The paper states (4) as $|f^tA_Lf|\le\sum_{v\in L}f^2(v)$ and remarks that it is an equality when loops are added, and an inequality in case a matching is added instead. This mission uses loops, so the equality is stated. It is the $L$-part of the decomposition (2) of $f^tA_Gf$ in the proof of Theorem 1.2.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 9, Section 2.4, eq. (4) and the sentence after it

import Mathlib
import Definitions.Def_ExplicitExpanders_Attach_IsNDLambda
import Definitions.Def_ExplicitExpanders_Attach_attachMatrix

namespace ExplicitExpanders.Attach

open Matrix

/-- Display (4) (arXiv:2003.11673v1, §2.4, p. 9), in the loop case, where it is an equality:
`fᵗ A_L f = ∑_{v∈L} f(v)²` for every real `f` on `V ⊕ Fin r`, with `L = V ∖ ⋃ᵢ W i`. -/
theorem eq_4 {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ} (W : Fin r → Finset V)
    (f : V ⊕ Fin r → ℝ) :
    f ⬝ᵥ (matL W *ᵥ f) = ∑ v ∈ loopSet W, f (Sum.inl v) ^ 2 := by sorry

end ExplicitExpanders.Attach
