-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/8223a5ef-7f6a-59f2-8cab-50b0eb6da373
-- title:
--   Injectivity of the Čech augmentation on Γ(V,W)
-- statement:
--   Let $R$ be a commutative ring, $V$ a scheme, and $\pi\colon V\to\operatorname{Spec}R$ a morphism; via the ring map $(\Gamma\text{-}\mathrm{Spec}$ comparison isomorphism inverted$)$ followed by $\pi^{\sharp}$ on sections over $\top$ restricted to an open, each $\Gamma(V,O)$ becomes an $R$-algebra, hence an $R$-module, and this is the module structure `moduleSections` used throughout. Let $W$ be an open subscheme of $V$ and let $K$ be an ordered affine cover of $W$, that is: a finite linearly ordered index type $\iota$, opens $U_i\le W$ of $V$ for $i\in\iota$, each $U_i$ affine, with $\bigsqcup_i U_i=\sup_i U_i=W$. The assertion is that the $R$-linear augmentation map $$\operatorname{aug}\colon \Gamma(V,W)\longrightarrow C^0(K)=\prod_{s\,:\,K.\mathrm{Idx}\,0}\Gamma(V,K.\mathrm{inter}\,s),$$ whose $s$-component is the restriction along $K.\mathrm{inter}\,s\le W$, is injective as a function. Here `K.Idx 0` is the type of $0$-dimensional increasing index tuples, so that its elements correspond to single members $U_i$ of the cover, and `K.inter s` is the corresponding open.
--
--   This is the separatedness (uniqueness) half of the sheaf axiom for $\mathcal O_V$ with respect to the cover $\{U_i\}$ of $W$: a section over $W$ is determined by its restrictions to the members of the cover. It provides exactness at the left end of the ordered Čech complex of $K$, and is used in the Leray-type comparison results for $\mathcal O$-module presheaves, among them [`AlgebraicGeometry.OModulePresheaf.Leray.rows_exact`](thm.html#AlgebraicGeometry.OModulePresheaf.Leray.rows_exact) and the zigzag lemmas for cochains with vanishing differential.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCoverOf_aug_injective.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCoverOf.aug_injective {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) {W : V.Opens} (K : V.OrderedAffineCoverOf W) : letI := Scheme.OrderedAffineCoverOf.moduleSections π; Function.Injective (K.aug π) := by sorry
