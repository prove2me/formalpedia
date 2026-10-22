-- Prove2me | Theorems.Thm_ConcreteSheaves_Quasitopos_lemma_48
-- name    : ConcreteSheaves.Quasitopos.lemma_48
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:19.520977+00:00
-- url     : https://prove2.me/theorems/96c0df10-f9cc-4674-8e57-33f55ed48047
-- title:
--   Lemma 48, p. 39 — concrete presheaves on a concrete site are separated
-- statement:
--   Let $D$ be a small category with a coverage $K$ and a terminal object $T$ (written $1$ in the paper), and suppose $(D,K,T)$ is a **concrete site**: representables are sheaves, $\operatorname{hom}(1,-)$ is faithful, and covering families are jointly surjective on points. Write $\underline{X}=X(1)$ for the underlying set of a presheaf $X$ and $\underline{\varphi}:\underline{D}\to\underline{X}$, $d\mapsto X(d)(\varphi)$, for the underlying function of a plot $\varphi\in X(D)$.
--
--   A presheaf $P$ is **separated** if, for every covering family $(f_i:D_i\to D)$, two plots $\varphi,\varphi'\in P(D)$ with $P(f_i)\varphi=P(f_i)\varphi'$ for all $i$ are equal. If $P$ is concrete, then
--
--   $$
--   P\ \text{is separated for every covering family of }K.
--   $$
--
--   Consequently sheafification of a concrete presheaf needs only one application of the plus construction.
--
--   **Formalization Note** The site is small ($D$ in universe $u$, presheaves valued in $\mathrm{Type}_u$), covering families are presieves, and the terminal domain is passed explicitly as $(T, h_T)$. Separatedness is Mathlib's `Presieve.IsSeparatedFor` on each covering presieve of the coverage.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, p. 39, Lemma 48

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits Opposite

universe u
variable {D : Type u} [SmallCategory D]

/-- Baez–Hoffnung, Lemma 48, p. 39. -/
theorem lemma_48 (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) (P : Dᵒᵖ ⥤ Type u) (hP : IsConcrete T P) :
    ∀ ⦃X : D⦄ (R : Presieve X), R ∈ K X → Presieve.IsSeparatedFor P R := by sorry

end ConcreteSheaves.Quasitopos
