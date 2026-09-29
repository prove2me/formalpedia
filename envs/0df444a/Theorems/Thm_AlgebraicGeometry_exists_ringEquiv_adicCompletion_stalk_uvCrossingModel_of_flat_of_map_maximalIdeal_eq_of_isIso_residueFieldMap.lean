-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_flat_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
-- name    : AlgebraicGeometry.exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_flat_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/83d78938-e49a-5224-9496-beb94ab42346
-- title:
--   Completed stalk over the crossing vertex is a UV-model
-- statement:
--   Let $O$ be a discrete valuation domain with a uniformiser $\varpi$, so that $\mathfrak m_O = (\varpi)$, let $E \ge 1$, let $w \in O^{\times}$ and put $a = w\varpi^{E}$. Write $\mathrm{CrossingQuotient}\,O\,a = O[X_0,X_1]/(X_0X_1 - a)$ and let `CrossingQuotient.crossingScheme a` be its spectrum. Let $Y$ be a scheme, $g : Y \to \operatorname{Spec}(O[X_0,X_1]/(X_0X_1-a))$ a morphism and $y$ a point of $Y$ whose stalk $B = \mathcal O_{Y,y}$ is Noetherian; assume the classes $U$ and $V$ of $X_0$ and $X_1$ both lie in the prime ideal of the image point $g(y)$, and that the induced map of stalks $\mathcal O_{g(y)} \to B$ is flat, carries the maximal ideal of $\mathcal O_{g(y)}$ onto the maximal ideal of $B$ after extension of ideals, and induces an isomorphism of residue fields. Writing $\varphi$ for the identification of $O[X_0,X_1]/(X_0X_1-a)$ with the global sections of its spectrum and $\mathrm{germ}$ for pullback along $g$ of a global section followed by the germ at $y$, the assertion is that there exist a discrete valuation domain $W$ which is complete for its maximal-ideal adic topology, a ring homomorphism $\sigma : O \to W$ with $\mathfrak m_W = (\sigma\varpi)$ and with $O \to W \to W/\mathfrak m_W$ surjective, and a ring isomorphism $$\iota : \widehat{B} \;\xrightarrow{\ \sim\ }\; W[[X_0,X_1]]/(X_0X_1 - (\sigma\varpi)^{E}),$$ where $\widehat B$ is the $\mathfrak m_B$-adic completion, such that: $\iota$ sends the image in $\widehat B$ of the germ of each constant $o \in O$ to the class of the constant power series $\sigma o$; it sends the image of the germ of $U$ to the class of $X_0$ times some unit of the quotient; and it sends the image of the germ of $V$ exactly to the class of $X_1$.
--
--   This is the branch-adapted local description of a point lying over the vertex of the plane crossing $uv = w\varpi^{E}$ under a morphism that is flat with trivial residue extension and unramified maximal ideal: the completed local ring is the crossing model $W[[U,V]]/(UV - \pi^{E})$, with the two branches matched to the coordinates $U$ and $V$ up to a unit. It is used to identify the completed local rings at the supersingular points of the models of modular curves studied in this development, via [`ModularCurve.XHDRModelAtP.isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart`](thm.html#ModularCurve.XHDRModelAtP.isNoetherianRing_stalk_and_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_flat_of_map_maximalIdeal_eq_of_isIso_residueFieldMap.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry
open IsLocalRing
open MvPolynomial ModularCurve

theorem AlgebraicGeometry.exists_ringEquiv_adicCompletion_stalk_uvCrossingModel_of_flat_of_map_maximalIdeal_eq_of_isIso_residueFieldMap
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (E : ℕ) (hE : 1 ≤ E) (w : Oˣ) (a : O) (ha : a = (w : O) * ϖ ^ E)
    (Y : Scheme.{0}) (g : Y ⟶ CrossingQuotient.crossingScheme a) (y : ↥Y)
    [IsNoetherianRing (Y.presheaf.stalk y)]
    (hy : CrossingQuotient.U a ∈ (g.base y).asIdeal ∧ CrossingQuotient.V a ∈ (g.base y).asIdeal)
    (hpt : (g.stalkMap y).hom.Flat ∧
      Ideal.map (g.stalkMap y).hom (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _ ∧
      IsIso (g.residueFieldMap y)) :
    letI φ : CrossingQuotient O a →+* Γ(CrossingQuotient.crossingScheme a, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O a))).inv.hom
    letI germ : Γ(CrossingQuotient.crossingScheme a, ⊤) → Y.presheaf.stalk y :=
      fun t => (Y.presheaf.germ ⊤ y trivial).hom ((g.appTop).hom t)
    letI B := Y.presheaf.stalk y
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : O →+* W)
      (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ})
      (_ : Function.Surjective ((IsLocalRing.residue W).comp σ))
      (ι : AdicCompletion (IsLocalRing.maximalIdeal B) B ≃+* UVCrossingModel W ((σ ϖ) ^ E)),
      (∀ o : O, ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (germ (φ (algebraMap O _ o)))) =
        UVCrossingModel.const ((σ ϖ) ^ E) (σ o)) ∧
      (∃ w' : (UVCrossingModel W ((σ ϖ) ^ E))ˣ,
        ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (germ (φ (CrossingQuotient.U a)))) =
          UVCrossingModel.U ((σ ϖ) ^ E) * w') ∧
      ι (algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B) (germ (φ (CrossingQuotient.V a)))) =
        UVCrossingModel.V ((σ ϖ) ^ E) := by sorry
