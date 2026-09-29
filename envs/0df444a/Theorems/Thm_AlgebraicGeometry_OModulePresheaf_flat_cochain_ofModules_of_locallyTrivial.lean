-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial
-- name    : AlgebraicGeometry.OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/e3ec0c2d-fdd9-523b-b5b5-4a2e2dbdb855
-- title:
--   Flatness of Čech cochains of a locally trivial module
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme and $\pi\colon V\to\operatorname{Spec}R$ a morphism which is flat and separated, and let $M$ be a sheaf of $\mathcal O_V$-modules. Assume $M$ is locally trivial in the following sense: every point $x$ of $V$ has an open neighbourhood $U$ such that the pullback of $M$ along the open immersion $U\hookrightarrow V$ is isomorphic to the unit sheaf of modules on $U$, i.e. to $\mathcal O_U$ itself. Let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $\iota$ together with opens $K.U\,i$ which are affine and satisfy $\bigsqcup_i K.U\,i=\top$, and let $i\in\mathbb N$. The conclusion is that the degree-$i$ cochain module of the presheaf `OModulePresheaf.ofModules π M` for $K$ is flat over $R$; concretely, this is the product $\prod_{s}\Gamma(M,\ K.\mathrm{inter}\ s)$ over the index type $K.\mathrm{Idx}\,i$ of $i$-simplices, where $K.\mathrm{inter}\ s=\bigwedge_j K.U(s_j)$ is the intersection of the cover members named by the entries of $s$, and where the $R$-module structure on sections of $M$ over an open $W$ is obtained by restriction of scalars along the algebra map $R\to\Gamma(V,W)$ induced by $\pi$.
--
--   This is the standard input that the Čech complex of a flat family, with coefficients in a sheaf that is locally isomorphic to the structure sheaf, consists of flat $R$-modules. It feeds the cohomology-and-base-change arguments for such presheaves, in particular the vanishing, Euler characteristic and base-change statements proved for `OModulePresheaf` over local and general base rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_flat_cochain_ofModules_of_locallyTrivial.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.flat_cochain_ofModules_of_locallyTrivial
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [Flat π] [IsSeparated π] (M : V.Modules)
    (htriv : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (K : V.OrderedAffineCover) (i : ℕ) :
    Module.Flat R ((OModulePresheaf.ofModules π M).cochain K i) := by sorry
