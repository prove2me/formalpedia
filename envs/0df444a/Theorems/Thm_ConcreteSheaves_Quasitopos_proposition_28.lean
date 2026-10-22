-- Prove2me | Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_28
-- name    : ConcreteSheaves.Quasitopos.proposition_28
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:29.340693+00:00
-- url     : https://prove2.me/theorems/3057430a-df6f-48ff-be7a-bd5318047b3d
-- title:
--   Proposition 28, p. 24 — the underlying-set functor DSpace → Set is faithful
-- statement:
--   Let $D$ be a small category with a coverage $K$ and a terminal object $T$ (written $1$ in the paper), and suppose $(D,K,T)$ is a **concrete site**: representables are sheaves, $\operatorname{hom}(1,-)$ is faithful, and covering families are jointly surjective on points. Write $\underline{X}=X(1)$ for the underlying set of a presheaf $X$ and $\underline{\varphi}:\underline{D}\to\underline{X}$, $d\mapsto X(d)(\varphi)$, for the underlying function of a plot $\varphi\in X(D)$.
--
--   A **$D$ space** is a concrete sheaf on $D$; maps of $D$ spaces are natural transformations. The underlying-set functor sends a $D$ space $X$ to $\underline X = X(1)$ and a map $f:X\to Y$ to $f_1:X(1)\to Y(1)$. Then
--
--   $$
--   \underline{\ \ }:\ \mathrm{DSpace}\longrightarrow\mathrm{Set}\quad\text{is faithful.}
--   $$
--
--   Thus a map of $D$ spaces is determined by its underlying function; this is the basic tool for computing monomorphisms and epimorphisms in $\mathrm{DSpace}$.
--
--   **Formalization Note** The site is small ($D$ in universe $u$, presheaves valued in $\mathrm{Type}_u$), covering families are presieves, and the terminal domain is passed explicitly as $(T, h_T)$. The functor is evaluation at $T$ composed with the inclusion of $D$ spaces into presheaves.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, p. 24, Proposition 28

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits Opposite

universe u
variable {D : Type u} [SmallCategory D]

/-- Baez–Hoffnung, Proposition 28, p. 24. -/
theorem proposition_28 (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    (underlying K T).Faithful := by sorry

end ConcreteSheaves.Quasitopos
