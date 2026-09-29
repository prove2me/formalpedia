-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ker
-- name    : AlgebraicGeometry.OModulePresheaf.isCoherent_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/038961a8-4a90-52b2-990e-5691b9708932
-- title:
--   Coherence of the kernel presheaf over a locally Noetherian base
-- statement:
--   Fix a commutative ring $R$ and a scheme $V$ over $\operatorname{Spec} R$, i.e. a morphism $\pi \colon V \to \operatorname{Spec} R$, and assume $V$ is locally Noetherian. Let $F$ and $G$ be module-presheaf data over $\pi$: for each open $U \subseteq V$ a type $F.\mathrm{obj}\,U$ carrying an abelian group structure, an $R$-module structure and a $\Gamma(V,U)$-module structure which are compatible as a scalar tower over the $R$-algebra structure on $\Gamma(V,U)$ induced by $\pi$, together with $R$-linear restriction maps $F.\mathrm{res}$ for $U \le U'$ that are semilinear for the restriction of sections, reflexive and transitive. Let $\varphi \colon F \to G$ be a morphism of such data, that is, a family of $R$-linear maps $\varphi.\mathrm{app}\,U \colon F.\mathrm{obj}\,U \to G.\mathrm{obj}\,U$ commuting with multiplication by sections over $U$ and with the restriction maps. Assume $F$ is coherent in the sense that for every affine open $U$ of $V$ the module $F.\mathrm{obj}\,U$ is finite over $\Gamma(V,U)$. The conclusion is that the open-by-open kernel $\ker \varphi$, whose value at $U$ is $\operatorname{ker}(\varphi.\mathrm{app}\,U)$ with the induced module structures and restrictions, is coherent in the same sense.
--
--   This is the standard closure property that coherence is inherited by kernels of morphisms, here in the form used for the explicit presheaf-level module data over a base $\operatorname{Spec} R$, with coherence taken as finite generation over $\Gamma(V,U)$ for each affine open $U$. It feeds the finiteness inputs of the Euler-characteristic computations for such module data, being used by the results on $\mathrm{eulerChar}$ of twists by pushforward units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_ker.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.isCoherent_ker {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsLocallyNoetherian V] {F G : OModulePresheaf π} (φ : OModulePresheaf.Hom F G) (hF : F.IsCoherent) : (OModulePresheaf.ker φ).IsCoherent := by sorry
