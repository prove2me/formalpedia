-- Prove2me | Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_34
-- name    : ConcreteSheaves.Quasitopos.proposition_34
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:41.546896+00:00
-- url     : https://prove2.me/theorems/97fa117c-a15d-4a11-beda-0ec8578d1ce4
-- title:
--   Proposition 34, p. 27 — strong monomorphisms are exactly the subspace inclusions
-- statement:
--   Let $D$ be a small category with a coverage $K$ and a terminal object $T$ (written $1$ in the paper), and suppose $(D,K,T)$ is a **concrete site**: representables are sheaves, $\operatorname{hom}(1,-)$ is faithful, and covering families are jointly surjective on points. Write $\underline{X}=X(1)$ for the underlying set of a presheaf $X$ and $\underline{\varphi}:\underline{D}\to\underline{X}$, $d\mapsto X(d)(\varphi)$, for the underlying function of a plot $\varphi\in X(D)$.
--
--   A map of $D$ spaces $i:A\to X$ makes $A$ a **subspace** of $X$ if for every plot $\varphi\in X(D)$ with $\underline\varphi(\underline D)\subseteq\underline i(\underline A)$ there is a unique plot $\psi\in A(D)$ with $i_D(\psi)=\varphi$. A monomorphism is **strong** if it has the unique diagonal lifting property against every epimorphism. For every map $i:A\to X$ of $D$ spaces,
--
--   $$
--   i\ \text{is a strong monomorphism}\iff i\ \text{makes }A\text{ a subspace of }X.
--   $$
--
--   This is what makes $\Omega$ a classifier for subspaces rather than for all monomorphisms.
--
--   **Formalization Note** The site is small ($D$ in universe $u$, presheaves valued in $\mathrm{Type}_u$), covering families are presieves, and the terminal domain is passed explicitly as $(T, h_T)$. Strong monomorphisms are Mathlib's `StrongMono` in the category of $D$ spaces (uniqueness of the diagonal is automatic for a mono); the subspace condition is the definition `IsSubspace`.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, p. 27, Proposition 34

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits Opposite

universe u
variable {D : Type u} [SmallCategory D]

/-- Baez–Hoffnung, Proposition 34, p. 27. -/
theorem proposition_34 (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) {A X : DSpace K T} (i : A ⟶ X) :
    StrongMono i ↔ IsSubspace i := by sorry

end ConcreteSheaves.Quasitopos
