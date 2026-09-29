-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal
-- name    : AlgebraicGeometry.Scheme.Modules.baseChangeHom_comp_horizontal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/88fe23e3-d1c3-5571-8887-c8e41ba0892d
-- title:
--   Horizontal pasting of base-change morphisms of module sheaves
-- statement:
--   Let $X, T, X', T', X'', T''$ be schemes and let $\pi : X \to T$, $\psi : T' \to T$, $\pi' : X' \to T'$, $g' : X' \to X$, $\psi' : T'' \to T'$, $\pi'' : X'' \to T''$, $g'' : X'' \to X'$ be morphisms of schemes. Assume $h_1 : g' \gg \pi = \pi' \gg \psi$, so that the right-hand square commutes, $h_2 : g'' \gg \pi' = \pi'' \gg \psi'$, so that the left-hand square commutes, and, as a separately supplied hypothesis, $h_{12} : (g'' \gg g') \gg \pi = \pi'' \gg (\psi' \gg \psi)$ for the outer rectangle. Let $F$ be a sheaf of $\mathcal{O}_X$-modules. Here, for a commutative square with data as in $h_1$, `baseChangeHom` denotes the component at the given module of the natural transformation underlying the two-square obtained as the mate, with respect to the two pullback $\dashv$ pushforward adjunctions, of the canonical two-square attached to the commutativity relation; it is a morphism $\psi^{*}\pi_{*}F \to \pi'_{*}g'^{*}F$. The assertion is that the base-change morphism of the outer rectangle, $(\psi' \gg \psi)^{*}\pi_{*}F \to \pi''_{*}(g'' \gg g')^{*}F$, equals the composite of: the inverse of the canonical isomorphism `pullbackComp` $\psi'$ $\psi$ at $\pi_{*}F$; the image under $\psi'^{*}$ of the base-change morphism of the right-hand square for $F$; the base-change morphism of the left-hand square for $g'^{*}F$; and the image under $\pi''_{*}$ of the canonical isomorphism `pullbackComp` $g''$ $g'$ at $F$.
--
--   This is the compatibility of the Beck–Chevalley base-change morphism for quasi-coherent (indeed arbitrary) sheaves of modules with horizontal pasting of two commutative squares along the base, with the canonical isomorphisms comparing iterated inverse images written out explicitly. It is used in the proof that the base-change morphism is an isomorphism whenever the square can be covered by pullback squares of a suitable local form (`isIso_baseChangeHom_of_forall_exists_isPullback`), where transitivity along a composite base change is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_horizontal.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.baseChangeHom_comp_horizontal
    {X T X' T' X'' T'' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    {ψ' : T'' ⟶ T'} {π'' : X'' ⟶ T''} {g'' : X'' ⟶ X'}
    (h₁ : g' ≫ π = π' ≫ ψ) (h₂ : g'' ≫ π' = π'' ≫ ψ') (h₁₂ : (g'' ≫ g') ≫ π = π'' ≫ (ψ' ≫ ψ))
    (F : X.Modules) :
    Scheme.Modules.baseChangeHom h₁₂ F =
      (Scheme.Modules.pullbackComp ψ' ψ).inv.app ((Scheme.Modules.pushforward π).obj F) ≫
        (Scheme.Modules.pullback ψ').map (Scheme.Modules.baseChangeHom h₁ F) ≫
          Scheme.Modules.baseChangeHom h₂ ((Scheme.Modules.pullback g').obj F) ≫
            (Scheme.Modules.pushforward π'').map ((Scheme.Modules.pullbackComp g'' g').hom.app F) := by sorry
