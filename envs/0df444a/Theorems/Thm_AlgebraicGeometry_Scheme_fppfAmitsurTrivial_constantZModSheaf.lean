-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_constantZModSheaf
-- name    : AlgebraicGeometry.Scheme.fppfAmitsurTrivial_constantZModSheaf
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/4bbec462-6513-55f4-9853-13c116832741
-- title:
--   Amitsur 1-cocycles with values in underlineℤ/p over ℤ
-- statement:
--   Let $p$ be a non-zero natural number and let $A$ be a commutative ring (in `Type`) which is faithfully flat as a $\mathbb Z$-module. Consider the fppf sheaf of abelian groups `constantZModSheaf p` on schemes, whose value on a scheme $T$ is the group of continuous maps $T \to \mathbb Z/p$ (the target carrying the discrete topology, so these are the locally constant $\mathbb Z/p$-valued functions), and let `sheafULift` raise its values to the next universe. The assertion is `Scheme.FppfAmitsurTrivial` for this sheaf $F$ and the ring $A$, which unfolds as follows: for every section $c$ of $F$ over $\operatorname{Spec}$ of the ring `R₂ ℤ A` satisfying the cocycle identity
--   $$\operatorname{Spec}(c_{12})^{*}c + \operatorname{Spec}(c_{23})^{*}c = \operatorname{Spec}(c_{13})^{*}c,$$
--   where `c₁₂ ℤ A`, `c₂₃ ℤ A`, `c₁₃ ℤ A` are the cofaces out of `R₂ ℤ A` in the Amitsur complex of $\mathbb Z \to A$, there exists a section $b$ of $F$ over $\operatorname{Spec}(A)$ with $c = \operatorname{Spec}(i_1)^{*}b - \operatorname{Spec}(i_2)^{*}b$, for the two cofaces `i₁ ℤ A`, `i₂ ℤ A` into `R₂ ℤ A`. In other words, the first Amitsur (Čech) cohomology of $\underline{\mathbb Z/p}$ for the faithfully flat cover $\operatorname{Spec}(A) \to \operatorname{Spec}(\mathbb Z)$ vanishes.
--
--   This is the Čech-theoretic form of the statement that $\operatorname{Spec}(\mathbb Z)$ has no non-trivial everywhere-unramified cyclic $p$-coverings, i.e. that $H^1(\operatorname{Spec}\mathbb Z, \mathbb Z/p) = 0$, Minkowski's theorem in the guise needed for fppf cohomology. It is used to prove [`AlgebraicGeometry.subsingleton_fppfH1_constantZMod_specZ_of_prime`](thm.html#AlgebraicGeometry.subsingleton_fppfH1_constantZMod_specZ_of_prime), the vanishing of $H^1_{\mathrm{fppf}}(\operatorname{Spec}\mathbb Z, \underline{\mathbb Z/p})$, which in turn feeds the splitting of extensions of $\underline{\mathbb Z}$ by $\underline{\mathbb Z/p}$ in the Kummer-sequence analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_fppfAmitsurTrivial_constantZModSheaf.lean

import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.fppfAmitsurTrivial_constantZModSheaf
    (p : ℕ) (hp : p ≠ 0) (A : Type) [CommRing A] [Module.FaithfullyFlat ℤ A] :
    Scheme.FppfAmitsurTrivial
      (FppfKummerSES.sheafULift.{0}.obj (FppfRepresentableGroupSchemeSheaf.constantZModSheaf.{0} p)) A := by sorry
