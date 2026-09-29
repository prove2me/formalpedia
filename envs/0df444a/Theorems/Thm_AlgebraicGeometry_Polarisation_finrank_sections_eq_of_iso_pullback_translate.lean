-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_finrank_sections_eq_of_iso_pullback_translate
-- name    : AlgebraicGeometry.Polarisation.finrank_sections_eq_of_iso_pullback_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/f7606f59-8ac0-5699-a435-138da8b3acda
-- title:
--   Translation invariance of dim_kΓ under a relative group law
-- statement:
--   Let $k$ be a field, let $A$ be a scheme and $f : A \to \operatorname{Spec} k$ a morphism, and let $L$ be a relative group law on $f$: for every test scheme $T$ and every $t : T \to \operatorname{Spec} k$, a multiplication, a unit and an inversion on the set of $\varphi : T \to A$ with $\varphi$ followed by $f$ equal to $t$, satisfying associativity, the two unit laws and left inversion, and with the multiplication natural in $(T,t)$ along composition with any $\psi : T' \to T$ satisfying $t' = \psi$ followed by $t$. Let $\mathcal M$ be an $\mathcal O_A$-module, let $x$ be a point of $A$ over the identity of $\operatorname{Spec} k$, i.e. $x : \operatorname{Spec} k \to A$ with $x$ followed by $f$ the identity, and write $T_x = L.\mathrm{translate}\,x : A \to A$ for the underlying morphism of $L$-multiplication of the identity point of $A$ by $f$ followed by $x$. Let $\mathcal N$ be an $\mathcal O_A$-module together with an isomorphism $e : \mathcal N \cong T_x^{*}\mathcal M$. Equip $\Gamma(A,\top)$ with the $k$-algebra structure coming from the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $k$ followed by $f$ on global sections, and equip $\Gamma(\mathcal M,\top)$ and $\Gamma(\mathcal N,\top)$ with the resulting $k$-module structures by restriction of scalars. Then $\dim_k \Gamma(\mathcal N,\top) = \dim_k \Gamma(\mathcal M,\top)$, as `Module.finrank`.
--
--   This is the invariance of $h^0$ under translation on a scheme with a relative group law: pulling a module back along a translation does not change the dimension of its space of global sections. It is used in the polarisation material, in the argument bounding Hom-spaces for modules isomorphic to tensor powers when the kernel of multiplication is finite and $h^0$ is positive.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_finrank_sections_eq_of_iso_pullback_translate.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationPicZero
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.finrank_sections_eq_of_iso_pullback_translate
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (𝓜 : A.Modules) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (𝓝 : A.Modules) (e : 𝓝 ≅ (Scheme.Modules.pullback (L.translate x)).obj 𝓜) :
    letI : Algebra k Γ(A, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ le_top).hom.toAlgebra
    letI : Module k Γ(𝓜, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
    letI : Module k Γ(𝓝, ⊤) := Module.compHom _ (algebraMap k Γ(A, ⊤))
    Module.finrank k Γ(𝓝, ⊤) = Module.finrank k Γ(𝓜, ⊤) := by sorry
