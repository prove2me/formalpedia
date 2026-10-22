-- Prove2me | Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_45
-- name    : ConcreteSheaves.Quasitopos.proposition_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:09.1548+00:00
-- url     : https://prove2.me/theorems/43368a4a-ffa5-485e-a850-24ccc9f79eae
-- title:
--   Proposition 45 — local cartesian closure
-- statement:
--   Let $(D,K,T)$ be a small concrete site. For every $D$ space $B$, the slice category of $D$ spaces over $B$ is cartesian closed:
--
--   $$
--   \forall B\in\mathrm{DSpace}(D),\quad
--   \mathrm{DSpace}(D)/B\text{ has finite products and }
--   (X\times_B-)\text{ has a right adjoint for every }X\to B.
--   $$
--
--   This is the paper's local cartesian closure assertion, including every base and every object over that base. It is one of the three categorical properties in the quasitopos conclusion.
--
--   **Formalization Note** A slice is Mathlib's `Over B`. The product functor uses $X\times_B-$, naturally isomorphic to the paper's $-\times_B X$. Its terminal object is canonical; the predicate explicitly supplies binary products. The site is small and uses presieves, with terminal-domain data $T$.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, pp. 32–33, Definitions 42–43 and Proposition 45

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits

universe u
variable {D : Type u} [SmallCategory D]

/-- Baez–Hoffnung, Proposition 45, p. 33. -/
theorem proposition_45 (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    IsLocallyCartesianClosed (DSpace K T) := by sorry

end ConcreteSheaves.Quasitopos
