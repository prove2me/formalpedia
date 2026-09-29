-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE
-- name    : AlgebraicGeometry.Scheme.Modules.unitAutSection_comap_refinement_eq_appLE
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/9120ff4e-c06c-5747-854f-4f46635f17f4
-- title:
--   Discrepancy section of a pulled-back Čech trivialisation restricts along h₀
-- statement:
--   Let $X$, $X'$, $X_0$, $X_0'$ be schemes, let $g : X_0 \to X$ and $g' : X_0' \to X'$ be affine morphisms, and let $h : X' \to X$, $h_0 : X_0' \to X_0$ satisfy $g \circ h_0 = h \circ g'$. Let $\mathcal U$ be a finite ordered affine cover of $X$ (a finite linearly ordered index type with affine opens covering $X$), $\mathcal W$ one of $X'$, and $\lambda : \mathcal W.\iota \to \mathcal U.\iota$ a map with $\mathcal W.U\,w \le h^{-1}(\mathcal U.U\,\lambda w)$ for all $w$. Let $M$ be a module sheaf on $X$, $\tau$ a Čech trivialisation of $M$ on $\mathcal U$, i.e. isomorphisms of the pullback of $M$ to each $\mathcal U.U\,a$ with the unit sheaf, and $\tau'$ a Čech trivialisation of $h^*M$ on $\mathcal W$. Fix $w$ and assume $\tau'\,w$ is the explicit composite obtained from $\tau\,\lambda w$ by pulling back along the induced morphism $\mathcal W.U\,w \to \mathcal U.U\,\lambda w$ (the comparison isomorphisms `pullbackComp`, `pullbackCongr` for the factorisation of $(\mathcal W.U\,w).\iota \circ h$ through $h \mid_{\mathcal U.U\,\lambda w}$, and `pullbackUnitIso`). Let $\varphi_0 : g^*M \cong \mathcal O_{X_0}$. Then the section of $\mathcal O_{X_0'}$ over $g'^{-1}(\mathcal W.U\,w)$ obtained by evaluating at $1$ the automorphism of the unit sheaf given by the inverse of the pulled-back trivialisation $(\tau'.\mathrm{comap}\,g')\,w$ followed by the transport of $\varphi_0$ along $g \circ h_0 = h \circ g'$ and restriction to that open, equals the image under $h_0^\sharp$ (the `appLE` map for $g'^{-1}(\mathcal W.U\,w) \le h_0^{-1}(g^{-1}(\mathcal U.U\,\lambda w))$, which follows from $hlam$ and the commutativity hypothesis) of the corresponding section over $g^{-1}(\mathcal U.U\,\lambda w)$ built from $(\tau.\mathrm{comap}\,g)\,\lambda w$ and $\varphi_0$.
--
--   This is the compatibility, under base change along $h$ and its closed-subscheme companion $h_0$, of the discrepancy sections measuring the failure of a Čech trivialisation on a cover to agree with a global trivialisation after pullback along an affine morphism. It feeds the discrepancy clause in the naturality statement [`AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback`](thm.html#AlgebraicGeometry.SmallExtension.exists_isPicDeformationCocycle_pullback_eq_unitPullback) for deformation cocycles of line bundles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_comap_refinement_eq_appLE.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

theorem AlgebraicGeometry.Scheme.Modules.unitAutSection_comap_refinement_eq_appLE
    {X X' X₀ X₀' : Scheme.{u}}
    (g : X₀ ⟶ X) [IsAffineHom g] (g' : X₀' ⟶ X') [IsAffineHom g']
    (h : X' ⟶ X) (h₀ : X₀' ⟶ X₀) (hh₀ : h₀ ≫ g = g' ≫ h)
    (𝒰 : X.OrderedAffineCover) (𝒲 : X'.OrderedAffineCover) (lam : 𝒲.ι → 𝒰.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒰.U (lam w))
    (M : X.Modules) (τ : Scheme.Modules.CechTrivialisation 𝒰 M)
    (τ' : Scheme.Modules.CechTrivialisation 𝒲 ((Scheme.Modules.pullback h).obj M))
    (w : 𝒲.ι) (hτ' : τ' w = (((Scheme.Modules.pullbackComp (𝒲.U w).ι h).app M) ≪≫
          ((Scheme.Modules.pullbackCongr
              (show (𝒲.U w).ι ≫ h = (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w))) ≫ (𝒰.U (lam w)).ι by
                rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι])).app M) ≪≫
          ((Scheme.Modules.pullbackComp (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w))) (𝒰.U (lam w)).ι).app M).symm ≪≫
          (Scheme.Modules.pullback (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w)))).mapIso (τ (lam w)) ≪≫
          Scheme.Modules.pullbackUnitIso (X'.homOfLE (hlam w) ≫ (h ∣_ 𝒰.U (lam w)))))
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf) :
    Scheme.Modules.unitAutSection ((𝒲.comap g').U w)
        ((τ'.comap g' w).symm ≪≫
          ((Scheme.Modules.pullback ((𝒲.comap g').U w).ι).mapIso (((Scheme.Modules.pullbackComp g' h).app M) ≪≫
          ((Scheme.Modules.pullbackCongr hh₀.symm).app M) ≪≫
          ((Scheme.Modules.pullbackComp h₀ g).app M).symm ≪≫
          (Scheme.Modules.pullback h₀).mapIso φ₀ ≪≫
          Scheme.Modules.pullbackUnitIso h₀) ≪≫
            Scheme.Modules.pullbackUnitIso ((𝒲.comap g').U w).ι)) =
      (h₀.appLE ((𝒰.comap g).U (lam w)) ((𝒲.comap g').U w)
          (show g' ⁻¹ᵁ 𝒲.U w ≤ h₀ ⁻¹ᵁ (g ⁻¹ᵁ 𝒰.U (lam w)) by
            rw [← Scheme.Hom.comp_preimage, hh₀, Scheme.Hom.comp_preimage]
            exact fun p hp => hlam w hp)).hom
        (Scheme.Modules.unitAutSection ((𝒰.comap g).U (lam w))
          ((τ.comap g (lam w)).symm ≪≫
            ((Scheme.Modules.pullback ((𝒰.comap g).U (lam w)).ι).mapIso φ₀ ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U (lam w)).ι))) := by sorry
