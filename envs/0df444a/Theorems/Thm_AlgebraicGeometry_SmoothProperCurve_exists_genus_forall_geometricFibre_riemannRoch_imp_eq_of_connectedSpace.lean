-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace
-- name    : AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/cdb8d803-5ba2-51bf-ad02-b8b86bf81e5c
-- title:
--   Constancy of the fibre genus over a connected Noetherian base
-- statement:
--   Let $R$ be a Noetherian commutative ring whose prime spectrum is a connected space, and let $c \colon C \to \operatorname{Spec} R$ be a morphism of schemes which is proper, smooth of relative dimension $1$ and geometrically integral. Let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} R \to C$ whose composite with $c$ is the identity, and let $\mathfrak{F}$ be finite-map chart data for $c$ and $\varepsilon$: affine opens $U, V$ with $U \sqcup V = C$, sections $f \in \Gamma(C,U)$, $g \in \Gamma(C,V)$ and an integer $m$, such that $U$ is exactly the complement of the image of $\varepsilon$, $U \cap V$ is simultaneously the basic open set of $f$ and of $g$, the restrictions of $f$ and $g$ to $U \cap V$ are mutually inverse, the $R$-algebra maps $R[T] \to \Gamma(C,U)$, $T \mapsto f$ and $R[T] \to \Gamma(C,V)$, $T \mapsto g$ are finite, and for every local $R$-algebra $S$ and every $s \in S$ the level set quotient $S \otimes_R \Gamma(C,U)$ modulo $(1 \otimes f - s \otimes 1)$ is finite and free of rank $m$ over $S$. The conclusion asserts the existence of a natural number $g$ with the following property: for every algebraically closed field $k$, every morphism $s \colon \operatorname{Spec} k \to \operatorname{Spec} R$, every field $L$ with a $k$-algebra structure, every curve model $M$ of $L/k$ (an integral scheme $M.C$ with a proper, smooth of relative dimension $1$ morphism to $\operatorname{Spec} k$, a ring isomorphism of $L$ with the function field of $M.C$ over $k$, a bijection of the closed points of $M.C$ with the places of $L/k$ matching stalks with valuation rings, and every finite set of points contained in an affine open), every isomorphism $e \colon M.C \cong C \times_{\operatorname{Spec} R} \operatorname{Spec} k$ whose composite with the second projection is the structure morphism $M.C \to \operatorname{Spec} k$, every divisor $K_c$ (a finitely supported $\mathbb{Z}$-valued function on the places of $L/k$) and every natural number $g'$: if $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for all divisors $D$ of $L/k$, where $\ell(D)$ is the $k$-dimension of the Riemann–Roch space of $D$ and $\deg$ is the degree homomorphism weighted by the residue degrees of the places, then $g' = g$. Thus any genus occurring in a Riemann–Roch formula for any geometric fibre of $c$ equals one and the same $g$; no existence of such $K_c$, $g'$ or of such a model is asserted here.
--
--   This is the constancy of the genus in a smooth proper family of curves over a connected base (local constancy of $\chi(\mathcal{O}_{C_s})$ for a flat proper family), in the form of a uniqueness statement for the genus appearing in Riemann–Roch over the geometric fibres. It is the global-base version of the corresponding statement over a local Noetherian base, and is used in the construction of the relative Picard scheme and of the Abel–Jacobi map on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve
open AlgebraicGeometry.SmoothProperCurve

theorem AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace
    (R : Type u) [CommRing R] [IsNoetherianRing R] [ConnectedSpace (PrimeSpectrum R)]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝔉 : SmoothProperCurve.FiniteMapData c ε) :
    ∃ g : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by sorry
