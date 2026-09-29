-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis
-- name    : AlgebraicGeometry.RelPicard.exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/29930810-9224-5224-a694-503fa4e58439
-- title:
--   Dual-number deformation of chartwise bases of f_*𝒪
-- statement:
--   Let $R$ be a commutative ring, let $c\colon C\to\operatorname{Spec}R$ and $c'\colon C'\to\operatorname{Spec}R$ be schemes over $R$, and let $A$ be an $R$-algebra. Let $\mathcal V$ and $\mathcal W$ be two-affine open covers of $C$ and $C'$ (each a pair of affine opens with union $\top$ and affine intersection); their base changes $\mathcal V_A$, $\mathcal W_A$ consist of the preimages of these opens under the first projections of $C_A=C\times_{\operatorname{Spec}R}\operatorname{Spec}A$ and $C'_A$. Let $f$ be a morphism over the identity of $A$, that is, a morphism $f\colon C'_A\to C_A$ commuting with the projections to $\operatorname{Spec}A$ and carrying each member of $\mathcal W_A$ into the corresponding member of $\mathcal V_A$, and let $f^\varepsilon$ be such a datum over the identity of the dual numbers $A[\varepsilon]$, so $f^\varepsilon\colon C'_{A[\varepsilon]}\to C_{A[\varepsilon]}$. Assume $f$ is an affine morphism, and assume the square formed by $f^\varepsilon$, the thickening projections $\sigma'\colon C'_{A[\varepsilon]}\to C'_A$ and $\sigma\colon C_{A[\varepsilon]}\to C_A$ (the base changes of $\operatorname{Spec}A[\varepsilon]\to\operatorname{Spec}A$ along $c'$ and $c$) and $f$ is cartesian, with $f^\varepsilon$ followed by $\sigma$ equal to $\sigma'$ followed by $f$. Let $d\in\mathbb N$, let $U\subseteq C_A$ be open, and let $U^\varepsilon=\sigma^{-1}(U)$. Let $e_1,\dots,e_d\in\Gamma(U,f_*\mathcal O_{C'_A})$, where $f_*\mathcal O_{C'_A}$ is the pushforward along $f$ of the unit module on $C'_A$, and suppose that for every open $W\le U$ the restrictions of the $e_i$ form a basis of $\Gamma(W,f_*\mathcal O_{C'_A})$ over $\Gamma(W,\mathcal O_{C_A})$ indexed by $\mathrm{Fin}\,d$. Then there exist $e^\varepsilon_1,\dots,e^\varepsilon_d\in\Gamma(U^\varepsilon,f^\varepsilon_*\mathcal O_{C'_{A[\varepsilon]}})$ whose restrictions to every open $W\le U^\varepsilon$ form a basis of $\Gamma(W,f^\varepsilon_*\mathcal O_{C'_{A[\varepsilon]}})$ over $\Gamma(W,\mathcal O_{C_{A[\varepsilon]}})$ indexed by $\mathrm{Fin}\,d$.
--
--   This is the statement that a chartwise free basis of the pushforward structure sheaf along an affine morphism lifts across a dual-number thickening, the square being cartesian; over the dual numbers the sections are the sections over $A$ tensored with $A[\varepsilon]$, so freeness of the same rank persists. It feeds the relative Picard infrastructure over dual numbers, being used in the identification of Čech $H^1$ germs with traces along a deformation class map and in the construction of isomorphisms of norm modules with the unit for curve changes over dual numbers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis.lean

import Mathlib
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.RelPicard AlgebraicGeometry.Scheme.TwoAffineOpenCover

theorem AlgebraicGeometry.RelPicard.exists_forall_basis_pushforward_dualNumberThickening_of_forall_basis
    {R : Type u} [CommRing R] {C C' : Scheme.{u}} (c : C ⟶ Spec (.of R)) (c' : C' ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover) (𝒲 : C'.TwoAffineOpenCover)
    (f : HomOver (RingHom.id A) (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒲.pullback c' A) (pullback.snd c' (specMap R A)))
    (fε : HomOver (RingHom.id (DualNumber A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A)))
      (𝒲.pullback c' (DualNumber A)) (pullback.snd c' (specMap R (DualNumber A))))
    [IsAffineHom f.hom]

    (hsq : IsPullback fε.hom (dualNumberThickening A 𝒲 c').hom (dualNumberThickening A 𝒱 c).hom f.hom)
    (d : ℕ) (U : (Limits.pullback c (specMap R A)).Opens)
    (Uε : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hUε : Uε = (dualNumberThickening A 𝒱 c).hom ⁻¹ᵁ U)

    (e : Fin d → Γ((Scheme.Modules.pushforward f.hom).obj (𝟙_ _), U))
    (he : ∀ (W : (Limits.pullback c (specMap R A)).Opens) (hW : W ≤ U),
      ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R A), W)
          Γ((Scheme.Modules.pushforward f.hom).obj (𝟙_ _), W),
        ∀ i, b i = ((Scheme.Modules.pushforward f.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (e i)) :
    ∃ eε : Fin d → Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), Uε),
      ∀ (W : (Limits.pullback c (specMap R (DualNumber A))).Opens) (hW : W ≤ Uε),
        ∃ b : Module.Basis (Fin d) Γ(Limits.pullback c (specMap R (DualNumber A)), W)
            Γ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _), W),
          ∀ i, b i = ((Scheme.Modules.pushforward fε.hom).obj (𝟙_ _)).presheaf.map (homOfLE hW).op (eε i) := by sorry
