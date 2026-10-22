-- Prove2me | Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_29
-- name    : ConcreteSheaves.Quasitopos.proposition_29
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:23.086828+00:00
-- url     : https://prove2.me/theorems/dd0d9972-ab51-4fd8-bf29-b2407609f93a
-- title:
--   Proposition 29, p. 25 — every representable presheaf is a D space
-- statement:
--   Let $D$ be a small category with a coverage $K$ and a terminal object $T$ (written $1$ in the paper), and suppose $(D,K,T)$ is a **concrete site**: representables are sheaves, $\operatorname{hom}(1,-)$ is faithful, and covering families are jointly surjective on points. Write $\underline{X}=X(1)$ for the underlying set of a presheaf $X$ and $\underline{\varphi}:\underline{D}\to\underline{X}$, $d\mapsto X(d)(\varphi)$, for the underlying function of a plot $\varphi\in X(D)$.
--
--   For every object $X$ of $D$, the representable presheaf $\operatorname{hom}(-,X):D^{\mathrm{op}}\to\mathrm{Set}$ is a $D$ space:
--
--   $$
--   \forall X\in D,\qquad \operatorname{hom}(-,X)\ \text{is a sheaf for }K\text{ and is concrete.}
--   $$
--
--   The result embeds the site into its category of generalized spaces via the Yoneda embedding.
--
--   **Formalization Note** The site is small ($D$ in universe $u$, presheaves valued in $\mathrm{Type}_u$), covering families are presieves, and the terminal domain is passed explicitly as $(T, h_T)$. The proposition's second sentence, that the underlying set of $\operatorname{hom}(-,X)$ is $\underline X=\operatorname{hom}(1,X)$, holds by definition in Lean (the value of the Yoneda presheaf at $T$ is the hom-set $T\to X$) and is not restated.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, p. 25, Proposition 29

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits Opposite

universe u
variable {D : Type u} [SmallCategory D]

/-- Baez–Hoffnung, Proposition 29, p. 25. -/
theorem proposition_29 (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    ∀ X : D, IsDSpace K T (yoneda.obj X) := by sorry

end ConcreteSheaves.Quasitopos
