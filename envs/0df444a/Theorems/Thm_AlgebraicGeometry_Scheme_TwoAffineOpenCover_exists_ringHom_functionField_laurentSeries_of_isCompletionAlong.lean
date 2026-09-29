-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ringHom_functionField_laurentSeries_of_isCompletionAlong
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_ringHom_functionField_laurentSeries_of_isCompletionAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/db5e71b4-4faf-55d9-a511-84d70d17565a
-- title:
--   Laurent chart at a rational point extends to the function field
-- statement:
--   Let $k$ be a field and $X$ an integral scheme, let $\mathcal V$ consist of two affine opens $U_0,U_1$ of $X$ with $U_0\sqcup U_1=\top$ and $U_0\sqcap U_1$ affine, and let $c:X\to\operatorname{Spec}k$ be smooth of relative dimension $1$, with $U_0\sqcap U_1$ non-empty as a scheme. Let $\sigma:\operatorname{Spec}k\to X$ satisfy $\sigma$ followed by $c$ equal to the identity, with the set-theoretic image of $\sigma$ contained in $U_0$. Write $A_0=\Gamma(X,U_0)$, $A_{01}=\Gamma(X,U_0\sqcap U_1)$, $\rho_0$ for the restriction $k$-algebra map $A_0\to A_{01}$, and $e$ for the $k$-algebra map $A_0\to k$ obtained by pulling back along $\sigma$. Let $\Lambda$ be a Laurent chart for this cover, i.e. a ring homomorphism $\Lambda:A_{01}\to k((t))$ carrying each $r\in k$ to the constant Hahn series $C(r)$, and assume $\Lambda$ is a completion along $(\rho_0,e)$: each $\Lambda(\rho_0 b)$ lies in the image of $k[[t]]$; for every $n$ and every power series $p$ some $b\in A_0$ has $\Lambda(\rho_0 b)$ agreeing with $p$ in all coefficients of degree $k<n$; and for every $n$ and $b\in A_0$ these coefficients all vanish exactly when $b\in(\ker e)^n$. Finally let $v$ be a place of $X.\mathrm{functionField}$ over $k$, that is a valuation subring containing the image of $k$, distinct from the whole field and a principal ideal ring, and assume its underlying subring is the image of the stalk of $X$ at the point $\sigma(\mathrm{closedPoint}\,k)$ in the function field. Then there is a ring homomorphism $\Lambda':X.\mathrm{functionField}\to k((t))$ such that $\Lambda'$ applied to the germ of any $y\in A_{01}$ in the function field equals $\Lambda(y)$, and such that for every $f$ in the function field, $f$ lies in the valuation subring of $v$ if and only if $\Lambda'(f)$ lies in the image of $k[[t]]$ in $k((t))$.
--
--   This is the passage from a Laurent expansion on the overlap of a two-chart cover to a Laurent expansion of the whole function field of the curve at the chosen $k$-rational point, with the power-series locus pinned down as the valuation ring of the place centred there. It is used in the construction of the Serre pairing on the two-chart Čech description and in the proof that residues vanish on coboundaries.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_ringHom_functionField_laurentSeries_of_isCompletionAlong.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoChartCechLaurentChart
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverSectional
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_ringHom_functionField_laurentSeries_of_isCompletionAlong {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ AlgebraicGeometry.Spec (.of k))
    [AlgebraicGeometry.SmoothOfRelativeDimension 1 c] [Nonempty (↑(𝒱.U0 ⊓ 𝒱.U1) : AlgebraicGeometry.Scheme.{u})]
    (σ : AlgebraicGeometry.Spec (.of k) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hU : Set.range σ.base ⊆ (𝒱.U0 : Set X))
    (Λ : (𝒱.cover c).LaurentChart)
    (hΛ : Λ.IsCompletionAlong (𝒱.cover c).ρ0 (AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionAlgHom σ hσ hU))
    [Algebra k X.functionField] (v : AlgebraicCurve.Place k X.functionField)
    (hv : (algebraMap (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint k))) X.functionField).range =
      v.toValuationSubring.toSubring) :
    ∃ Λ' : X.functionField →+* LaurentSeries k,
      (∀ y : (𝒱.cover c).A01, Λ' ((X.germToFunctionField (𝒱.U0 ⊓ 𝒱.U1)).hom y) = Λ.expand y) ∧
        (∀ f : X.functionField, f ∈ v.toValuationSubring ↔ Λ' f ∈ (HahnSeries.ofPowerSeries ℤ k).range) := by sorry
