-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_pair_of_pullback_map_eq
-- name    : AlgebraicGeometry.Scheme.Modules.pullback_map_conj_eq_trivialization_pair_of_pullback_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/65606f1b-076f-5f3a-af66-1c64a31f6917
-- title:
--   Restriction preserves normalisation: one module, two structure maps
-- statement:
--   Let $B,A,Y,Y_2,T,T_2$ be schemes and let $e : B \to A$, $\iota,\kappa : Y \to A$, $\iota_2,\kappa_2 : Y_2 \to A$ be morphisms. Let $\varepsilon : T \to Y$ and $p,q : T \to B$ satisfy $\iota \circ \varepsilon = e \circ p$ and $\kappa \circ \varepsilon = e \circ q$, and let $\varepsilon_2 : T_2 \to Y_2$ and $p_2,q_2 : T_2 \to B$ satisfy $\iota_2 \circ \varepsilon_2 = e \circ p_2$ and $\kappa_2 \circ \varepsilon_2 = e \circ q_2$. Let $j : Y_2 \to Y$ with $\iota \circ j = \iota_2$ and $\kappa \circ j = \kappa_2$, and let $\lambda : T_2 \to T$ with $j \circ \varepsilon_2 = \varepsilon \circ \lambda$, $p \circ \lambda = p_2$ and $q \circ \lambda = q_2$. Let $L$ be a sheaf of modules on $A$, equipped with an isomorphism $hLe : e^*L \cong \mathcal{O}_B$ onto the unit module `SheafOfModules.unit B.ringCatSheaf`, and let $\varphi : \iota^*L \cong \kappa^*L$. For a pair $(\varepsilon,p)$ as above write $\tau_p$ for the composite isomorphism $\varepsilon^*\iota^*L \cong (\iota \circ \varepsilon)^*L \cong (e \circ p)^*L \cong p^*e^*L \cong p^*\mathcal{O}_B \cong \mathcal{O}_T$, built from the canonical comparison isomorphisms `Scheme.Modules.pullbackComp` and `Scheme.Modules.pullbackCongr` (the latter induced by the stated equality of morphisms), the pullback along $p$ of $hLe$, and `Scheme.Modules.pullbackUnitIso`, which identifies the pullback of the unit module with the unit module; define $\tau_q$, $\tau_{p_2}$, $\tau_{q_2}$ likewise. Assume $\varphi$ is normalised along $\varepsilon$, i.e. $\varepsilon^*\varphi = \tau_p$ followed by $\tau_q^{-1}$. The conclusion is that the transported isomorphism $\iota_2^*L \cong j^*\iota^*L \xrightarrow{\,j^*\varphi\,} j^*\kappa^*L \cong \kappa_2^*L$, formed with the same canonical comparisons for $j$, is normalised along $\varepsilon_2$: its pullback along $\varepsilon_2$ equals $\tau_{p_2}$ followed by $\tau_{q_2}^{-1}$.
--
--   This is a coherence statement for rigidified (normalised) isomorphisms between pullbacks of a single module sheaf along two different structure maps, asserting that the normalisation condition is preserved when the base is restricted along $j$ and the rigidifying data are transported along $\lambda$. It is used in [`AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_cocycle_of_rigidified`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_cocycle_of_rigidified), in the verification of the cocycle condition for rigidified line bundles underlying the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_pair_of_pullback_map_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullback_map_conj_eq_trivialization_pair_of_pullback_map_eq
    {B A Y Y₂ T T₂ : Scheme.{u}} (e : B ⟶ A) (ι κ : Y ⟶ A) (ι₂ κ₂ : Y₂ ⟶ A)
    (ε : T ⟶ Y) (p q : T ⟶ B) (hp : ε ≫ ι = p ≫ e) (hq : ε ≫ κ = q ≫ e)
    (ε₂ : T₂ ⟶ Y₂) (p₂ q₂ : T₂ ⟶ B) (hp₂ : ε₂ ≫ ι₂ = p₂ ≫ e) (hq₂ : ε₂ ≫ κ₂ = q₂ ≫ e)
    (j : Y₂ ⟶ Y) (hjι : j ≫ ι = ι₂) (hjκ : j ≫ κ = κ₂)
    (lam : T₂ ⟶ T) (hlam : ε₂ ≫ j = lam ≫ ε) (hlamp : lam ≫ p = p₂) (hlamq : lam ≫ q = q₂)
    (L : A.Modules)
    (hLe : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (φ : (Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback κ).obj L)
    (hφ : (Scheme.Modules.pullback ε).map φ.hom =
        ((Scheme.Modules.pullbackComp ε ι).app L ≪≫ (Scheme.Modules.pullbackCongr hp).app L ≪≫
            ((Scheme.Modules.pullbackComp p e).app L).symm ≪≫ (Scheme.Modules.pullback p).mapIso hLe ≪≫
            Scheme.Modules.pullbackUnitIso p).hom ≫
        ((Scheme.Modules.pullbackComp ε κ).app L ≪≫ (Scheme.Modules.pullbackCongr hq).app L ≪≫
            ((Scheme.Modules.pullbackComp q e).app L).symm ≪≫ (Scheme.Modules.pullback q).mapIso hLe ≪≫
            Scheme.Modules.pullbackUnitIso q).inv) :
    (Scheme.Modules.pullback ε₂).map
        (((Scheme.Modules.pullbackComp j ι).app L ≪≫ (Scheme.Modules.pullbackCongr hjι).app L).symm ≪≫
          (Scheme.Modules.pullback j).mapIso φ ≪≫
          ((Scheme.Modules.pullbackComp j κ).app L ≪≫ (Scheme.Modules.pullbackCongr hjκ).app L)).hom =
      ((Scheme.Modules.pullbackComp ε₂ ι₂).app L ≪≫ (Scheme.Modules.pullbackCongr hp₂).app L ≪≫
          ((Scheme.Modules.pullbackComp p₂ e).app L).symm ≪≫ (Scheme.Modules.pullback p₂).mapIso hLe ≪≫
          Scheme.Modules.pullbackUnitIso p₂).hom ≫
      ((Scheme.Modules.pullbackComp ε₂ κ₂).app L ≪≫ (Scheme.Modules.pullbackCongr hq₂).app L ≪≫
          ((Scheme.Modules.pullbackComp q₂ e).app L).symm ≪≫ (Scheme.Modules.pullback q₂).mapIso hLe ≪≫
          Scheme.Modules.pullbackUnitIso q₂).inv := by sorry
