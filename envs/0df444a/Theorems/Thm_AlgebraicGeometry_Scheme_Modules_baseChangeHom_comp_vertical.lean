-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_vertical
-- name    : AlgebraicGeometry.Scheme.Modules.baseChangeHom_comp_vertical
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/55a252cc-d824-5bc5-a8eb-5ba27ea3d006
-- title:
--   Base-change morphism under vertical pasting of squares
-- statement:
--   Let $X, Y, T, X', Y', T'$ be schemes and let $\rho : X \to Y$, $\sigma : Y \to T$, $\rho' : X' \to Y'$, $\sigma' : Y' \to T'$, $g' : X' \to X$, $k' : Y' \to Y$, $\psi : T' \to T$ be morphisms of schemes, subject to three commutativity hypotheses: $\rho \circ g' = k' \circ \rho'$ (the upper square, `htop`), $\sigma \circ k' = \psi \circ \sigma'$ (the lower square, `hbot`), and $(\sigma \circ \rho) \circ g' = \psi \circ (\sigma' \circ \rho')$ (the outer square, `h`), the last being assumed rather than deduced from the first two. Let $\mathcal F$ be a sheaf of $\mathcal O_X$-modules. Here, for a commutative square, `baseChangeHom` denotes the component at the given module of the mate, formed with respect to the pullback–pushforward adjunctions, of the canonical two-square of pullback functors; for the outer square it is a morphism $\psi^*(\sigma\rho)_*\mathcal F \to (\sigma'\rho')_* g'^*\mathcal F$. The assertion is that this morphism for the outer square equals the composite of: $\psi^*$ applied to the inverse at $\mathcal F$ of the canonical isomorphism `pushforwardComp` comparing $\sigma_*\rho_*$ with $(\sigma\rho)_*$, giving $\psi^*(\sigma\rho)_*\mathcal F \to \psi^*\sigma_*\rho_*\mathcal F$; followed by the base-change morphism of the lower square at $\rho_*\mathcal F$, landing in $\sigma'_* k'^*\rho_*\mathcal F$; followed by $\sigma'_*$ applied to the base-change morphism of the upper square at $\mathcal F$, landing in $\sigma'_*\rho'_* g'^*\mathcal F$; followed by the canonical isomorphism `pushforwardComp` for $\rho', \sigma'$ at $g'^*\mathcal F$, landing in $(\sigma'\rho')_* g'^*\mathcal F$.
--
--   This is the compatibility of the base-change (Beck–Chevalley) morphism for quasi-coherent-style sheaves of modules with vertical pasting of commutative squares of schemes, with the composition isomorphisms for direct images made explicit. It is used when a base-change morphism for a family is compared with the one obtained after factoring the structure morphism, for instance in [`AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_eq_zero_iff`](thm.html#AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_eq_zero_iff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_vertical.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.baseChangeHom_comp_vertical
    {X Y T X' Y' T' : Scheme.{u}} {ρ : X ⟶ Y} {σ : Y ⟶ T} {ρ' : X' ⟶ Y'} {σ' : Y' ⟶ T'}
    {g' : X' ⟶ X} {k' : Y' ⟶ Y} {ψ : T' ⟶ T}
    (htop : g' ≫ ρ = ρ' ≫ k') (hbot : k' ≫ σ = σ' ≫ ψ) (h : g' ≫ (ρ ≫ σ) = (ρ' ≫ σ') ≫ ψ)
    (F : X.Modules) :
    Scheme.Modules.baseChangeHom h F =
      (Scheme.Modules.pullback ψ).map ((Scheme.Modules.pushforwardComp ρ σ).inv.app F) ≫
        Scheme.Modules.baseChangeHom hbot ((Scheme.Modules.pushforward ρ).obj F) ≫
          (Scheme.Modules.pushforward σ').map (Scheme.Modules.baseChangeHom htop F) ≫
            (Scheme.Modules.pushforwardComp ρ' σ').hom.app ((Scheme.Modules.pullback g').obj F) := by sorry
