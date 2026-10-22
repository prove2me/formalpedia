-- Prove2me | Theorems.Thm_ConcreteSheaves_Quasitopos_proposition_30
-- name    : ConcreteSheaves.Quasitopos.proposition_30
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:21.670984+00:00
-- url     : https://prove2.me/theorems/7c9f01d5-5b2c-4af0-8f6c-aa003e81136b
-- title:
--   Proposition 30, p. 26 — the presheaf Ω(D) = 2^D is a D space
-- statement:
--   Let $D$ be a small category with a coverage $K$ and a terminal object $T$ (written $1$ in the paper), and suppose $(D,K,T)$ is a **concrete site**: representables are sheaves, $\operatorname{hom}(1,-)$ is faithful, and covering families are jointly surjective on points. Write $\underline{X}=X(1)$ for the underlying set of a presheaf $X$ and $\underline{\varphi}:\underline{D}\to\underline{X}$, $d\mapsto X(d)(\varphi)$, for the underlying function of a plot $\varphi\in X(D)$.
--
--   Let $\Omega$ be the presheaf with $\Omega(D)=2^{\underline D}$, the set of functions $\underline D=\operatorname{hom}(1,D)\to 2=\{0,1\}$, and, for $f:C\to D$, $\Omega(f)(\varphi)=\varphi\circ\underline f$. Then
--
--   $$
--   \Omega\ \text{is a } D \text{ space.}
--   $$
--
--   This $\Omega$ is the object that classifies strong monomorphisms (subspaces) in $\mathrm{DSpace}$ (Proposition 40).
--
--   **Formalization Note** The site is small ($D$ in universe $u$, presheaves valued in $\mathrm{Type}_u$), covering families are presieves, and the terminal domain is passed explicitly as $(T, h_T)$. The presheaf is the definition `omegaPresheaf`, with $2$ encoded as `Bool`; its values and restriction maps are the first two clauses of the proposition, and the theorem asserts the remaining claim, that it is a concrete sheaf.
-- source:
--   Baez–Hoffnung, Convenient categories of smooth spaces, arXiv:0807.1704v4, p. 26, Proposition 30

import Mathlib
import Definitions.Def_ConcreteSheaves_Quasitopos_Setting

namespace ConcreteSheaves.Quasitopos

open CategoryTheory CategoryTheory.Limits Opposite

universe u
variable {D : Type u} [SmallCategory D]

/-- Baez–Hoffnung, Proposition 30, p. 26. -/
theorem proposition_30 (K : Coverage D) (T : D) (hT : IsTerminal T)
    (hK : IsConcreteSite K T hT) :
    IsDSpace K T (omegaPresheaf T) := by sorry

end ConcreteSheaves.Quasitopos
