-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
-- name    : AlgebraicGeometry.Scheme.Modules.pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/b90f67fe-8189-50b0-9ee4-518ee6206e81
-- title:
--   Rigidified isomorphism stays rigidified under compatible restriction
-- statement:
--   Let $B$, $A$, $Y$, $Y_2$, $T$, $T_2$ be schemes and let $e : B \to A$, $\iota : Y \to A$, $\iota_2 : Y_2 \to A$, $\varepsilon : T \to Y$, $p : T \to B$, $\varepsilon_2 : T_2 \to Y_2$, $p_2 : T_2 \to B$, $j : Y_2 \to Y$ and $\mathrm{lam} : T_2 \to T$ be morphisms satisfying $\varepsilon$ followed by $\iota$ equals $p$ followed by $e$, $\varepsilon_2$ followed by $\iota_2$ equals $p_2$ followed by $e$, $j$ followed by $\iota$ equals $\iota_2$, $\varepsilon_2$ followed by $j$ equals $\mathrm{lam}$ followed by $\varepsilon$, and $\mathrm{lam}$ followed by $p$ equals $p_2$. Let $L$, $M$ be sheaves of modules on $A$, together with isomorphisms $h_{L,e}$, $h_{M,e}$ of $e^*L$, $e^*M$ with the unit module $\mathcal O_B$ on $B$, and let $\varphi : \iota^*L \cong \iota^*M$. For a module $N$ on $A$ trivialised along $e$ by $h$ and a datum $(\varepsilon,p)$ as above, write $\tau_N$ for the composite isomorphism $\varepsilon^*\iota^*N \cong (\varepsilon\iota)^*N \cong (pe)^*N \cong p^*e^*N \cong p^*\mathcal O_B \cong \mathcal O_T$ built from the pseudofunctoriality isomorphisms `Scheme.Modules.pullbackComp`, the comparison `Scheme.Modules.pullbackCongr` attached to the relevant commuting square, $p^*h$, and `Scheme.Modules.pullbackUnitIso`. Assume $\varepsilon^*\varphi$ equals $\tau_L$ followed by $\tau_M^{-1}$. Then the same holds after restriction along $j$: the $\varepsilon_2$-pullback of the isomorphism $\iota_2^*L \cong j^*\iota^*L \xrightarrow{j^*\varphi} j^*\iota^*M \cong \iota_2^*M$, where the outer identifications come from `pullbackComp` and `pullbackCongr` for $j$ and $\iota$, equals the corresponding composite $\tau_{2,L}$ followed by $\tau_{2,M}^{-1}$ formed from $\varepsilon_2$, $p_2$, $h_{L,e}$ and $h_{M,e}$.
--
--   This is a pure pseudofunctoriality statement for pullback of sheaves of modules on schemes: it says that the condition of being rigidified along a test map, in the shape used in the gluing data for isomorphisms of invertible modules, is stable under a morphism of pieces covered by a compatible morphism of test objects. It is used in the construction of isomorphisms of invertible modules from local data and in the verification of the associated cocycle condition, which feed into the rigidified line bundle formalism for relative Picard functors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullback_map_conj_eq_trivialization_of_pullback_map_eq_trivialization
    {B A Y Y₂ T T₂ : Scheme.{u}} (e : B ⟶ A) (ι : Y ⟶ A) (ι₂ : Y₂ ⟶ A)
    (ε : T ⟶ Y) (p : T ⟶ B) (hp : ε ≫ ι = p ≫ e)
    (ε₂ : T₂ ⟶ Y₂) (p₂ : T₂ ⟶ B) (hp₂ : ε₂ ≫ ι₂ = p₂ ≫ e)
    (j : Y₂ ⟶ Y) (hj : j ≫ ι = ι₂) (lam : T₂ ⟶ T) (hlam : ε₂ ≫ j = lam ≫ ε) (hlamp : lam ≫ p = p₂)
    (L M : A.Modules)
    (hLe : (Scheme.Modules.pullback e).obj L ≅ SheafOfModules.unit B.ringCatSheaf)
    (hMe : (Scheme.Modules.pullback e).obj M ≅ SheafOfModules.unit B.ringCatSheaf)
    (φ : (Scheme.Modules.pullback ι).obj L ≅ (Scheme.Modules.pullback ι).obj M)
    (hφ : (Scheme.Modules.pullback ε).map φ.hom =
        ((Scheme.Modules.pullbackComp ε ι).app L ≪≫ (Scheme.Modules.pullbackCongr hp).app L ≪≫
            ((Scheme.Modules.pullbackComp p e).app L).symm ≪≫ (Scheme.Modules.pullback p).mapIso hLe ≪≫
            Scheme.Modules.pullbackUnitIso p).hom ≫
        ((Scheme.Modules.pullbackComp ε ι).app M ≪≫ (Scheme.Modules.pullbackCongr hp).app M ≪≫
            ((Scheme.Modules.pullbackComp p e).app M).symm ≪≫ (Scheme.Modules.pullback p).mapIso hMe ≪≫
            Scheme.Modules.pullbackUnitIso p).inv) :
    (Scheme.Modules.pullback ε₂).map
        (((Scheme.Modules.pullbackComp j ι).app L ≪≫ (Scheme.Modules.pullbackCongr hj).app L).symm ≪≫
          (Scheme.Modules.pullback j).mapIso φ ≪≫
          ((Scheme.Modules.pullbackComp j ι).app M ≪≫ (Scheme.Modules.pullbackCongr hj).app M)).hom =
      ((Scheme.Modules.pullbackComp ε₂ ι₂).app L ≪≫ (Scheme.Modules.pullbackCongr hp₂).app L ≪≫
          ((Scheme.Modules.pullbackComp p₂ e).app L).symm ≪≫ (Scheme.Modules.pullback p₂).mapIso hLe ≪≫
          Scheme.Modules.pullbackUnitIso p₂).hom ≫
      ((Scheme.Modules.pullbackComp ε₂ ι₂).app M ≪≫ (Scheme.Modules.pullbackCongr hp₂).app M ≪≫
          ((Scheme.Modules.pullbackComp p₂ e).app M).symm ≪≫ (Scheme.Modules.pullback p₂).mapIso hMe ≪≫
          Scheme.Modules.pullbackUnitIso p₂).inv := by sorry
