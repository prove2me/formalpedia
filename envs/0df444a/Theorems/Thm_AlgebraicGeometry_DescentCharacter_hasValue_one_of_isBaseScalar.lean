-- Prove2me | Theorems.Thm_AlgebraicGeometry_DescentCharacter_hasValue_one_of_isBaseScalar
-- name    : AlgebraicGeometry.DescentCharacter.hasValue_one_of_isBaseScalar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.863777+00:00
-- url     : https://prove2.me/theorems/c40d0fbb-0126-5275-b1d4-f45ff180d3ce
-- title:
--   Base-scalar automorphisms have descent value one
-- statement:
--   Let $X$ and $Y$ be schemes, $R$ a commutative ring, and $f\colon X \to \operatorname{Spec} R$ a morphism of schemes. Let $T\colon X \to X$ and $q\colon X \to Y$ be morphisms with $T$ followed by $q$ equal to $q$ (the hypothesis $h$) and $T$ followed by $f$ equal to $f$ (the hypothesis $hT$). Let $M$ be an object of `Y.Modules`, let $\gamma$ be an isomorphism from `(Scheme.Modules.pullback q).obj M` to itself, and let $c \in R$. Assume `IsBaseScalar f γ.hom c`: for every open $U \subseteq X$ and every section $s$ of the pulled-back module over $U$, the component of $\gamma$ at $U$ sends $s$ to $(\mathrm{baseSection}\ f\ c\ U) \cdot s$, where $\mathrm{baseSection}\ f\ c\ U \in \Gamma(X,U)$ is the restriction to $U$ of the image of $c$ under the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism followed by $f$ on global sections. The conclusion is `HasValue f h γ 1`, that is, the discrepancy automorphism $\gamma^{-1}$ followed by the $T$-translate `translateIso h γ` of $\gamma$ acts on every section over every open $U$ as multiplication by $\mathrm{baseSection}\ f\ 1\ U$.
--
--   This says that the descent character at $T$ of an identification which is multiplication by a constant pulled back from the base takes the value $1$; combined with multiplicativity of values it expresses the independence of the descent character from the choice of trivialisation. It is used in the construction of the torsion character attached to a polarisation, via [`AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_pullback_schemeNsmul_two_trivial_hasValue_translate`](thm.html#AlgebraicGeometry.Polarisation.exists_rigidifiedLineBundle_pullback_schemeNsmul_two_trivial_hasValue_translate) and [`AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial`](thm.html#AlgebraicGeometry.Polarisation.exists_torsionCharacter_two_hasValue_translate_of_pullback_schemeNsmul_two_trivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_DescentCharacter_hasValue_one_of_isBaseScalar.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_DescentCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.DescentCharacter

universe u

theorem AlgebraicGeometry.DescentCharacter.hasValue_one_of_isBaseScalar
    {X Y : Scheme.{u}} {R : Type u} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {T : X ⟶ X} {q : X ⟶ Y} (h : T ≫ q = q) (hT : T ≫ f = f) {M : Y.Modules}
    (γ : (Scheme.Modules.pullback q).obj M ≅ (Scheme.Modules.pullback q).obj M) (c : R)
    (hγ : IsBaseScalar f γ.hom c) :
    HasValue f h γ 1 := by sorry
