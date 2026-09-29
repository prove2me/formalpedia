-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_nonempty_pullback_iso_tensorUnit
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_nonempty_pullback_iso_tensorUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/57eb2578-cfb7-5b33-9e97-c52c08a2c60a
-- title:
--   Triviality of an invertible module descends along a field map
-- statement:
--   Let $k$ be a field, let $A$ be a scheme and let $f : A \to \operatorname{Spec} k$ be a morphism satisfying the bundle of abelian-scheme properties `AbelianSchemePropertyBundle`, that is: $f$ is smooth, $f$ is proper, for every point $s$ of $\operatorname{Spec} k$ the fibre $f^{-1}(s)$ (preimage under the map of underlying spaces) is connected, and there exists a relative group law for $f$, i.e. a functorial group structure on the sets of $T$-points over $\operatorname{Spec} k$, natural in $T$. Let $\mathcal M$ be a module on $A$ which is invertible in the sense of `Scheme.Modules.IsInvertible`: every point of $A$ has an open neighbourhood $U$ such that the restriction of $\mathcal M$ along the inclusion $U \hookrightarrow A$ is isomorphic to the unit module of the sheaf of rings of $U$. Let $k'$ be a further field and $\varphi : k \to k'$ a ring homomorphism. Assume that the pullback of $\mathcal M$ along the first projection $A \times_{\operatorname{Spec} k} \operatorname{Spec} k' \to A$ is isomorphic to the monoidal unit of the category of modules on that fibre product. Then $\mathcal M$ is isomorphic to the monoidal unit of $A$'s modules, i.e. $\mathcal M$ is trivial. (All statements of isomorphism are phrased as nonemptiness of the relevant type of isomorphisms.)
--
--   This is the descent step saying that triviality of a line bundle on an abelian scheme over a field is insensitive to base change along an arbitrary extension of the base field; no algebraic closedness or finiteness of the extension is assumed. It is used in [`AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_isPullback`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_of_nonempty_pullback_iso_of_isPullback), which compares two invertible modules after base change rather than comparing one with the unit.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_nonempty_pullback_iso_tensorUnit.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_CerednikDrinfeld_QMCanonicalPol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_nonempty_pullback_iso_tensorUnit
    (k : Type) [Field k] {A : Scheme} (f : A ⟶ Spec (CommRingCat.of k)) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (k' : Type) [Field k'] (φ : k →+* k')
    (h : Nonempty ((Scheme.Modules.pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom φ)))).obj 𝓜 ≅
      𝟙_ ((Limits.pullback f (Spec.map (CommRingCat.ofHom φ))).Modules))) :
    Nonempty (𝓜 ≅ 𝟙_ A.Modules) := by sorry
