-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_tensor
-- name    : AlgebraicGeometry.DescentCharacter.hasValue_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/b7e90be7-334e-598e-9732-795a499931b4
-- title:
--   Multiplicativity of descent-character values under tensor product
-- statement:
--   Let $X$ and $Y$ be schemes, $R$ a commutative ring, and $f\colon X\to\operatorname{Spec}(R)$ a morphism giving the base ring. Let $T\colon X\to X$ and $q\colon X\to Y$ be morphisms with $T$ followed by $q$ equal to $q$, witnessed by $h$. Let $N,M,N',M'$ be modules on $Y$, and let $\beta\colon q^{*}N\cong q^{*}M$ and $\beta'\colon q^{*}N'\cong q^{*}M'$ be isomorphisms of modules on $X$ (pullback being `Scheme.Modules.pullback q`). Let $c,c'\in R$, and assume $\beta$ has value $c$ and $\beta'$ has value $c'$ in the sense of `HasValue`: the discrepancy endomorphism of $q^{*}M$, namely $\beta^{-1}$ followed by the transport `translateIso h β` of $\beta$ along $h$, acts on every section $s\in\Gamma(q^{*}M,U)$ over every open $U\subseteq X$ as multiplication by `baseSection f c U`, the section of the structure sheaf obtained from $c$ via $f$, and likewise for $\beta'$, $c'$ on $q^{*}M'$. The conclusion is that the composite isomorphism $q^{*}(N\otimes N')\cong q^{*}N\otimes q^{*}N'\xrightarrow{\beta\otimes\beta'}q^{*}M\otimes q^{*}M'\cong q^{*}(M\otimes M')$, the outer identifications being `Scheme.Modules.pullbackTensorObjIso` (the inverse of the monoidal structure isomorphism of the pullback functor), has value $c\,c'$ in the same sense.
--
--   This is the multiplicativity, under tensor product of the compared pairs of modules, of the character attached to a pair $(q,T)$ by comparing an isomorphism of pullbacks with its translate; classically it expresses that the descent character of $N\otimes N'$ is the product of those of $N$ and $N'$. It is used in the construction of the torsion character in [`AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial`](thm.html#AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial), where it supplies the monoidal-coherence step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_hasValue_tensor.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.DescentCharacter

theorem AlgebraicGeometry.DescentCharacter.hasValue_tensor
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q)
    {N M N' M' : Y.Modules}
    (β : (Scheme.Modules.pullback q).obj N ≅ (Scheme.Modules.pullback q).obj M)
    (β' : (Scheme.Modules.pullback q).obj N' ≅ (Scheme.Modules.pullback q).obj M')
    (c c' : R) (hβ : HasValue f h β c) (hβ' : HasValue f h β' c') :
    HasValue f h
      (Scheme.Modules.pullbackTensorObjIso q N N' ≪≫ (β ⊗ᵢ β') ≪≫ (Scheme.Modules.pullbackTensorObjIso q M M').symm)
      (c * c') := by sorry
