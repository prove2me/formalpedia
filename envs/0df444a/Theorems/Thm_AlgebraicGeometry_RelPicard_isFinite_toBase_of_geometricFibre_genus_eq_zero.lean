-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_isFinite_toBase_of_geometricFibre_genus_eq_zero
-- name    : AlgebraicGeometry.RelPicard.isFinite_toBase_of_geometricFibre_genus_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/1306d808-792a-5a71-9709-f9eda88a3513
-- title:
--   Genus-zero geometric fibres force JtoSpec k finite
-- statement:
--   Let $k$ be a field and $c\colon C\to\operatorname{Spec} k$ a proper morphism of schemes which is smooth of relative dimension one and geometrically integral, and let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} k\to C$ whose composite with $c$ is the identity. Let $J$ be a relative $\operatorname{Pic}^0$ designation for $c$: a scheme together with a structure morphism `J.toBase` to $\operatorname{Spec} k$ and a zero section splitting it. Assume `h`, that $J$ represents the subcondition `algEquivZeroCut` of the $\varepsilon$-rigidified relative Picard presheaf of $c$, whose value at $t\colon T\to\operatorname{Spec} k$ consists of the rigidified invertible modules $M$ on $C\times_k T$ such that for every algebraically closed field $k'$ and every $s\colon\operatorname{Spec} k'\to T$ the restriction of $M.L$ to the corresponding geometric fibre satisfies `IsAlgEquivZero`; concretely, `h` supplies a Poincaré rigidified bundle on $C\times_k J$ lying in the condition, the property that pullback of it along morphisms $T\to J$ over $\operatorname{Spec} k$ realises every such $M$ by a unique morphism, and triviality of its pullback along the zero section. Assume `hpr`, that `J.toBase` is proper, and assume the genus-zero hypothesis `hg`: for every algebraically closed field $k'$, every $s\colon\operatorname{Spec} k'\to\operatorname{Spec} k$, every field extension $L/k'$, every curve model $M$ of $L/k'$ (an integral scheme, proper and smooth of relative dimension one over $k'$, with function field identified with $L$ and closed points in bijection with the places), every isomorphism $e\colon M.C\cong C\times_k\operatorname{Spec} k'$ compatible with the projections to $\operatorname{Spec} k'$, every divisor $K_c$ of $L/k'$ and every $g'\in\mathbb{N}$ satisfying $\ell(D)-\ell(K_c-D)=\deg D+1-g'$ for all divisors $D$, one has $g'=0$. Then `J.toBase` is a finite morphism.
--
--   This is the degenerate case "the Jacobian of a curve of genus zero is a point", in the form of finiteness of $J\to\operatorname{Spec} k$ rather than of an isomorphism. It supplies the genus-zero branch of the construction of a finite morphism from $J$ to projective space by a power of the theta bundle, and is cited by [`AlgebraicGeometry.RelPicard.exists_finiteBySections_tensorPow_thetaBundle_of_isAlgClosed`](thm.html#AlgebraicGeometry.RelPicard.exists_finiteBySections_tensorPow_thetaBundle_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_isFinite_toBase_of_geometricFibre_genus_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.isFinite_toBase_of_geometricFibre_genus_eq_zero
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (J : RelativePic0Designation k c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) J)
    (hpr : IsProper J.toBase)
    (hg : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (s : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k))
      (L : Type u) [Field L] [Algebra k' L] (M : CurveModel k' L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k' L) (g' : ℕ),
      (∀ D : Divisor k' L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = 0) :
    IsFinite J.toBase := by sorry
