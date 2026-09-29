-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_forall_geometricFibre_riemannRoch_imp_eq_of_isAlgClosed
-- name    : AlgebraicGeometry.SmoothProperCurve.forall_geometricFibre_riemannRoch_imp_eq_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/e25c7f79-15f1-50ee-a231-3e7809f60c5f
-- title:
--   Genus of C is the genus of all its geometric fibres
-- statement:
--   Let $k$ be an algebraically closed field and let $c \colon C \to \operatorname{Spec} k$ be a morphism of schemes that is proper, smooth of relative dimension $1$ and geometrically integral. Let $\varepsilon$ be a section of $c$, i.e. a morphism $\operatorname{Spec} k \to C$ whose composite with $c$ is the identity, and let $\mathfrak{F}$ be a `FiniteMapData` for $c$ and $\varepsilon$: a pair of affine opens $U, V$ with $U \sqcup V = \top$, $U$ exactly the complement of the image of $\varepsilon$, sections $f \in \Gamma(C,U)$ and $g \in \Gamma(C,V)$ with $U \sqcap V$ equal to both basic opens $D(f)$ and $D(g)$ and with the restrictions of $f$ and $g$ mutually inverse there, the induced $k$-algebra maps $k[X] \to \Gamma(C,U)$, $X \mapsto f$, and $k[X] \to \Gamma(C,V)$, $X \mapsto g$, finite, and a rank $m$ such that for every local $k$-algebra $S$ and every $s \in S$ the quotient $S \otimes_k \Gamma(C,U)$ by $(1 \otimes f - s \otimes 1)$ is free of rank $m$ over $S$. Let $g \in \mathbb{N}$ and assume: for every field $L$ with a $k$-algebra structure, every `CurveModel` $M$ of $L$ over $k$ (an integral scheme $M.C$, proper and smooth of relative dimension $1$ over $\operatorname{Spec} k$, with a ring isomorphism of $L$ with the function field of $M.C$ compatible with $k$, a bijection between the closed points of $M.C$ and the places of $L/k$ matching stalks with valuation subrings, and every finite set of points contained in an affine open), every isomorphism of schemes $e \colon M.C \cong C$ with $e$ followed by $c$ equal to $M.\mathrm{toBase}$, every divisor $K_c$ of $L/k$ (a finitely supported $\mathbb{Z}$-valued function on places) and every $g' \in \mathbb{N}$, if $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ holds for all divisors $D$ of $L/k$, where $\ell$ is the $k$-dimension of the Riemann–Roch space and $\deg$ is the degree homomorphism weighting each place by its residue degree, then $g' = g$. The conclusion: for every algebraically closed field $k'$, every morphism $s \colon \operatorname{Spec} k' \to \operatorname{Spec} k$, every field $L$ with a $k'$-algebra structure, every `CurveModel` $M$ of $L$ over $k'$, every isomorphism $e \colon M.C \cong C \times_{\operatorname{Spec} k} \operatorname{Spec} k'$ with $e$ followed by the second projection equal to $M.\mathrm{toBase}$, every divisor $K_c$ of $L/k'$ and every $g' \in \mathbb{N}$ satisfying $\ell(D) - \ell(K_c - D) = \deg D + 1 - g'$ for all divisors $D$ of $L/k'$, one has $g' = g$.
--
--   This is the constancy of the genus in a smooth proper family of curves, specialised to a base that is the spectrum of an algebraically closed field: the Riemann–Roch genus of $C$ itself, formulated through function-field models, governs the genus of the base change of $C$ along an arbitrary algebraically closed point of the base. It converts the field-level genus hypothesis used by the Jacobian constructions into the geometric-fibre form required by the relative Picard statements [`AlgebraicGeometry.RelPicard.exists_finiteBySections_tensorPow_thetaBundle_of_isAlgClosed`](thm.html#AlgebraicGeometry.RelPicard.exists_finiteBySections_tensorPow_thetaBundle_of_isAlgClosed), [`AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_poincare_eq_zero_iff`](thm.html#AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_poincare_eq_zero_iff) and [`AlgebraicGeometry.RelPicard.nonempty_translate_thetaBundle_tensor_iso`](thm.html#AlgebraicGeometry.RelPicard.nonempty_translate_thetaBundle_tensor_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmoothProperCurve_forall_geometricFibre_riemannRoch_imp_eq_of_isAlgClosed.lean

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

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra AlgebraicCurve

theorem AlgebraicGeometry.SmoothProperCurve.forall_geometricFibre_riemannRoch_imp_eq_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) (𝔉 : SmoothProperCurve.FiniteMapData c ε)
    (g : ℕ)
    (hg : ∀ (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ C)
      (_ : e.hom ≫ c = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g) :
    ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] (s : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k))
      (L : Type u) [Field L] [Algebra k' L] (M : CurveModel k' L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k' L) (g' : ℕ),
      (∀ D : Divisor k' L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by sorry
