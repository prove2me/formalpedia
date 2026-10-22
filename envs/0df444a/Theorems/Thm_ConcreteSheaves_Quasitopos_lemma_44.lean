-- Prove2me | Theorems.Thm_ConcreteSheaves_Quasitopos_lemma_44
-- name    : ConcreteSheaves.Quasitopos.lemma_44
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:13.495691+00:00
-- url     : https://prove2.me/theorems/42f0de92-60f5-4ad9-bba2-82fe428935f5
-- title:
--   Lemma 44, p. 33 — the inclusion X ×_A Y → X × Y is a strong monomorphism
-- statement:
--   Let $D$ be a small category with a coverage $K$ and a terminal object $T$ (written $1$ in the paper), and suppose $(D,K,T)$ is a **concrete site**: representables are sheaves, $\operatorname{hom}(1,-)$ is faithful, and covering families are jointly surjective on points. Write $\underline{X}=X(1)$ for the underlying set of a presheaf $X$ and $\underline{\varphi}:\underline{D}\to\underline{X}$, $d\mapsto X(d)(\varphi)$, for the underlying function of a plot $\varphi\in X(D)$.
--
--   Let $f:X\to A$ and $g:Y\to A$ be maps of $D$ spaces and let $m:X\times_A Y\to X\times Y$ be the map induced by the two pullback projections (on underlying sets, the inclusion $\underline{X\times_A Y}\hookrightarrow\underline{X\times Y}$). Then
--
--   $$
--   m:\ X\times_A Y\longrightarrow X\times Y\ \text{is a strong monomorphism in }\mathrm{DSpace}.
--   $$
--
--   The lemma shows that the fibre product, which is the product in a slice $\mathrm{DSpace}/B$, carries the subspace structure inherited from the product.
--
--   **Formalization Note** The site is small ($D$ in universe $u$, presheaves valued in $\mathrm{Type}_u$), covering families are presieves, and the terminal domain is passed explicitly as $(T, h_T)$. The pullback and product are those of the category of $D$ spaces; their existence is taken as instance arguments `[HasPullback f g]` and `[HasBinaryProduct X Y]` (they exist by Proposition 39), so the statement does not depend on an unproved instance. Any choice of these limits gives an isomorphic $m$.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, p. 33, Lemma 44

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits Opposite

universe u
variable {D : Type u} [SmallCategory D]

/-- Baez–Hoffnung, Lemma 44, p. 33. -/
theorem lemma_44 (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) {X Y A : DSpace K T} (f : X ⟶ A) (g : Y ⟶ A)
    [HasPullback f g] [HasBinaryProduct X Y] :
    StrongMono (prod.lift (pullback.fst f g) (pullback.snd f g)) := by sorry

end ConcreteSheaves.Quasitopos
