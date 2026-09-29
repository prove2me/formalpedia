-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_iso_tensorUnit_of_fibrewiseAlgEquivZero_of_genus_eq_zero
-- name    : AlgebraicGeometry.RelPicard.nonempty_iso_tensorUnit_of_fibrewiseAlgEquivZero_of_genus_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/0515fbaa-bde0-5d91-b6f9-5e6a339fdf72
-- title:
--   Triviality of rigidified genus-zero bundles algebraically equivalent to zero
-- statement:
--   Let $R$ be a commutative ring and $c \colon C \to \operatorname{Spec} R$ a proper morphism which is smooth of relative dimension $1$ and geometrically integral, and let $\varepsilon$ be a section of $c$, that is a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity. Assume the genus-zero hypothesis `hg`: for every algebraically closed field $k$, every $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$, every field extension $L$ of $k$, every `CurveModel k L` $M$ (a smooth proper integral curve over $k$ together with an isomorphism of $L$ with its function field over $k$, a bijection of its closed points with the places of $L/k$ matching stalks with valuation subrings, and the property that every finite set of points lies in an affine open), every isomorphism $e \colon M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ compatible with the projections to $\operatorname{Spec} k$, every divisor $K_c$ of $L/k$ and every $g' \in \mathbb{N}$: if $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for all divisors $D$ (here $\ell$ is the $k$-dimension of the Riemann–Roch space and $\deg$ the sum of coefficients weighted by residue degrees), then $g' = 0$. Let $K$ be an algebraically closed field, $t \colon \operatorname{Spec} K \to \operatorname{Spec} R$, and let $M$ be a rigidified line bundle for $(c, \varepsilon, t)$: a module sheaf $M.L$ on $C \times_{\operatorname{Spec} R} \operatorname{Spec} K$ which is invertible (every point has an open neighbourhood on which its restriction is isomorphic to the unit) and whose pullback along the rigidifying section $\operatorname{Spec} K \to C \times_{\operatorname{Spec} R} \operatorname{Spec} K$ determined by $\varepsilon$ is isomorphic to the unit. Assume `FibrewiseAlgEquivZero M`: for every algebraically closed field $k$ and every $s \colon \operatorname{Spec} k \to \operatorname{Spec} K$, the restriction of $M.L$ to the geometric fibre over $s$ satisfies `IsAlgEquivZero`, i.e. there are a geometrically integral $T' \to \operatorname{Spec} k$ locally of finite type, an invertible module on the product of the fibre with $T'$, and two $k$-points of $T'$ at which that module specialises to the unit and to the given restriction respectively. Then $M.L$ is isomorphic to the unit object of the monoidal category of modules on $C \times_{\operatorname{Spec} R} \operatorname{Spec} K$.
--
--   This is the statement $\operatorname{Pic}^0(\mathbb{P}^1) = 0$ in the form needed for the rigidified relative Picard presheaf: over an algebraically closed field, a rigidified line bundle in the algebraic-equivalence-to-zero cut on a genus-zero curve is trivial. It is used in the proof that the relative Picard functor has finite structural morphism when all geometric fibres have genus zero ([`AlgebraicGeometry.RelPicard.isFinite_toBase_of_geometricFibre_genus_eq_zero`](thm.html#AlgebraicGeometry.RelPicard.isFinite_toBase_of_geometricFibre_genus_eq_zero)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_nonempty_iso_tensorUnit_of_fibrewiseAlgEquivZero_of_genus_eq_zero.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra AlgebraicCurve
open AlgebraicGeometry.RelPicard

theorem AlgebraicGeometry.RelPicard.nonempty_iso_tensorUnit_of_fibrewiseAlgEquivZero_of_genus_eq_zero
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = 0)
    (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : FibrewiseAlgEquivZero M) :
    Nonempty (M.L ≅ 𝟙_ (pullback c t).Modules) := by sorry
