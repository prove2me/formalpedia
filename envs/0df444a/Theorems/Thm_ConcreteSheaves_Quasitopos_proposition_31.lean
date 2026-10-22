-- Prove2me | Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_31
-- name    : ConcreteSheaves.Quasitopos.proposition_31
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:37.889768+00:00
-- url     : https://prove2.me/theorems/ddedf63f-5f91-4822-937f-b2f750a5927f
-- title:
--   Proposition 31, p. 26 — monos and epis in DSpace are the injective and surjective maps
-- statement:
--   Let $D$ be a small category with a coverage $K$ and a terminal object $T$ (written $1$ in the paper), and suppose $(D,K,T)$ is a **concrete site**: representables are sheaves, $\operatorname{hom}(1,-)$ is faithful, and covering families are jointly surjective on points. Write $\underline{X}=X(1)$ for the underlying set of a presheaf $X$ and $\underline{\varphi}:\underline{D}\to\underline{X}$, $d\mapsto X(d)(\varphi)$, for the underlying function of a plot $\varphi\in X(D)$.
--
--   For every map $f:X\to Y$ of $D$ spaces, with underlying function $\underline f=f_1:\underline X\to\underline Y$,
--
--   $$
--   f\ \text{mono}\iff \underline f\ \text{injective},\qquad f\ \text{epi}\iff \underline f\ \text{surjective}.
--   $$
--
--   This identifies the monomorphisms and epimorphisms of $\mathrm{DSpace}$ concretely and is used to analyse strong monomorphisms.
--
--   **Formalization Note** The site is small ($D$ in universe $u$, presheaves valued in $\mathrm{Type}_u$), covering families are presieves, and the terminal domain is passed explicitly as $(T, h_T)$. Mono and epi are taken in the category of $D$ spaces (a full subcategory of presheaves); $\underline f$ is the component of the natural transformation $f$ at $T$.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, p. 26, Proposition 31

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits Opposite

universe u
variable {D : Type u} [SmallCategory D]

/-- Baez–Hoffnung, Proposition 31, p. 26. -/
theorem proposition_31 (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) {X Y : DSpace K T} (f : X ⟶ Y) :
    (Mono f ↔ Function.Injective (f.hom.app (op T))) ∧
      (Epi f ↔ Function.Surjective (f.hom.app (op T))) := by sorry

end ConcreteSheaves.Quasitopos
