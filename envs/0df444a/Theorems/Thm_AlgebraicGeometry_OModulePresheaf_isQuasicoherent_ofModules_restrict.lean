-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_restrict
-- name    : AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_restrict
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/63b8e804-f600-57bd-b8c3-78192d04a6f7
-- title:
--   Quasi-coherence of the sections datum restricts to opens
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $\pi \colon X \to \operatorname{Spec}(R)$ a morphism of schemes, and $N$ an $\mathcal{O}_X$-module (an object of `X.Modules`). Consider the $\mathcal{O}$-module presheaf `ofModules π N` over $\pi$: it assigns to an open $U \subseteq X$ the sections $\Gamma(N, U)$, with its $\Gamma(X,U)$-module structure, the $R$-module structure obtained from $\pi$ through the algebra map $R \to \Gamma(X,U)$, and the presheaf restriction maps as the transition maps. The hypothesis `hN` is that this datum satisfies `IsQuasicoherent`, that is: for every affine open $U \subseteq X$ and every $f \in \Gamma(X,U)$, first, each $x \in \Gamma(N, X_f)$ over the basic open $X_f$ satisfies $y|_{X_f} = (f^n|_{X_f}) \cdot x$ for some $n \in \mathbb{N}$ and some $y \in \Gamma(N,U)$, and second, each $y \in \Gamma(N,U)$ with $y|_{X_f} = 0$ is annihilated by $f^n$ for some $n \in \mathbb{N}$. Let $W \subseteq X$ be an open subset, with $W.\iota$ the open immersion of the corresponding open subscheme. The conclusion is that the analogous datum `ofModules (W.ι ≫ π) (N.restrict W.ι)`, formed from the restricted module $N|_W$ over the composite $W \to X \to \operatorname{Spec}(R)$, again satisfies `IsQuasicoherent`.
--
--   This is the statement that quasi-coherence, in the elementwise form used here (restriction to a basic open is surjective up to multiplication by powers of $f$, with $f$-power torsion kernel), is inherited by open subschemes; no separatedness or finiteness assumption enters. It is used in the Čech-theoretic part of the development, where exactness of the rows and columns of the iterated Čech complexes of a quasi-coherent datum is proved after passing to members of an open cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_restrict.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_ofModules_restrict
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R))
    (N : X.Modules) (hN : (OModulePresheaf.ofModules π N).IsQuasicoherent) (W : X.Opens) :
    (OModulePresheaf.ofModules (W.ι ≫ π) (N.restrict W.ι)).IsQuasicoherent := by sorry
