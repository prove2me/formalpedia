-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_nonempty_pullback_one_pol_iso_unit_of_pullback
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.nonempty_pullback_one_pol_iso_unit_of_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/7742a5e1-7e66-5227-adba-2ffac7bfbe74
-- title:
--   Triviality of the polarisation at the zero section descends along base change
-- statement:
--   Fix natural numbers $g,d,n$ and commutative rings $S,S'$ (both in the lowest universe), a ring homomorphism $\varphi : S \to S'$, and polarised abelian schemes $u$ over $S$ and $v$ over $S'$ in the project's sense: each consists of a scheme $A$ with a structure morphism $f$ to $\operatorname{Spec}$ of the base, a commutative relative group law on the functor of points of $f$, smoothness, properness and connectedness of the fibres together with existence of a relative group law, fibres of topological Krull dimension $g$, a family $P : \mathrm{Fin}(2g) \to$ sections killed by $n$ which is independent and spanning on all algebraically closed geometric fibres, and a module `pol` on $A$ which is invertible, admits a closed immersion by sections of a projective presentation over the base, and has geometric fibre $H^0$-rank $d$. Assume $h$: $v$ is a pullback of $u$ along $\varphi$, i.e. there are a morphism $g_A : v.A \to u.A$ making the square over $\operatorname{Spec}\varphi$ cartesian, compatible with the group laws on $T$-points, carrying each $P_i$ of $v$ to the base change of $P_i$ of $u$, and such that $g_A^{*}(u.\mathrm{pol})$ is isomorphic to $v.\mathrm{pol}$. Assume further that the pullback along $\operatorname{Spec}\varphi$ of the pullback of $u.\mathrm{pol}$ along the unit section $0_u$ of $u$'s group law admits an isomorphism to the unit sheaf of modules on $\operatorname{Spec} S'$. The conclusion is that the pullback of $v.\mathrm{pol}$ along the unit section $0_v$ likewise admits an isomorphism to the unit sheaf of modules on $\operatorname{Spec} S'$; both hypothesis and conclusion are stated as nonemptiness of the type of such isomorphisms, so no particular isomorphism is specified.
--
--   This is the statement that the rigidification datum of a polarisation — triviality of its restriction along the zero section — is preserved under base change of polarised abelian schemes. It is used in the descent arguments for polarised abelian schemes along faithfully flat base change, namely by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_descent_and_iso_of_faithfullyFlat_of_three_le_type0`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_descent_and_iso_of_faithfullyFlat_of_three_le_type0) and [`AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.iso_of_iso_of_isPullback_of_faithfullyFlat_of_three_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_IsPullback_nonempty_pullback_one_pol_iso_unit_of_pullback.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.IsPullback.nonempty_pullback_one_pol_iso_unit_of_pullback
    {g d n : ℕ} {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    (u : PolarisedAbelianScheme g d n S) (v : PolarisedAbelianScheme g d n S')
    (h : PolarisedAbelianScheme.IsPullback φ u v)

    (hu : Nonempty ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom φ))).obj
      ((Scheme.Modules.pullback (u.L.one (𝟙 _)).1).obj u.pol) ≅ SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf)) :
    Nonempty ((Scheme.Modules.pullback (v.L.one (𝟙 _)).1).obj v.pol ≅ SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf) := by sorry
