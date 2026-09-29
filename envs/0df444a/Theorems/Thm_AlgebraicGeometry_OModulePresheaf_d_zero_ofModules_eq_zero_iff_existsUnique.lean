-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique
-- name    : AlgebraicGeometry.OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/f677b681-022e-59e6-9387-a1b8c99d6043
-- title:
--   Degree-zero Čech cocycles are families of restrictions
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, $\pi\colon V\to\operatorname{Spec} R$ a morphism of schemes, and $M$ a sheaf of $\mathcal O_V$-modules on $V$. Let $K$ be an ordered affine cover of $V$: a finite index type $\iota$ with a linear order, together with opens $K.U\,i$ that are affine and satisfy $\bigsqcup_i K.U\,i=\top$. Consider the presheaf of $R$-modules `OModulePresheaf.ofModules π M` attached to these data, whose value on an open $U$ is $\Gamma(M,U)$, with $R$-action obtained from the algebra map $R\to\Gamma(V,U)$ induced by $\pi$ and with restriction maps those of the presheaf of $M$. Let $c$ be a $0$-cochain of this presheaf for $K$, that is, a family assigning to each $s\in K.\mathrm{Idx}\,0$ — a strictly monotone map $\mathrm{Fin}\,1\to\iota$, so in effect a single index — a section $c\,s\in\Gamma(M,K.\mathrm{inter}\,s)$, where $K.\mathrm{inter}\,s=\bigsqcap_j K.U\,(s\,j)$. The assertion is that the Čech differential `d K 0` annihilates $c$ if and only if there is a unique global section $x\in\Gamma(M,\top)$ whose restriction along $K.\mathrm{inter}\,s\le\top$ equals $c\,s$ for every $s\in K.\mathrm{Idx}\,0$.
--
--   This is the sheaf axiom for $M$ read off in degree zero of the ordered (alternating) Čech complex: the kernel of $d^0$ consists exactly of the families of restrictions of a global section, which is thereby unique. It is used in the project to identify the zeroth Čech cohomology with global sections, for instance in the exactness of the columns of the iterated Čech complex for quasi-coherent data and in the finiteness and base-change statements derived from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_d_zero_ofModules_eq_zero_iff_existsUnique.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.d_zero_ofModules_eq_zero_iff_existsUnique
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (M : V.Modules)
    (K : V.OrderedAffineCover) (c : (OModulePresheaf.ofModules π M).cochain K 0) :
    (OModulePresheaf.ofModules π M).d K 0 c = 0 ↔
      ∃! x : Γ(M, ⊤), ∀ s : K.Idx 0, c s = M.presheaf.map (homOfLE (le_top : K.inter s ≤ ⊤)).op x := by sorry
