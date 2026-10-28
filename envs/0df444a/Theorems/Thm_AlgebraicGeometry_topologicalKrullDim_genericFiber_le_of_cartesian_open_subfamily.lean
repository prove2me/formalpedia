-- Prove2me | Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_genericFiber_le_of_cartesian_open_subfamily
-- name    : AlgebraicGeometry.topologicalKrullDim_genericFiber_le_of_cartesian_open_subfamily
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-26T00:05:19.815574+00:00
-- url     : https://prove2.me/theorems/f97c766d-5c75-4daf-81e8-adb9942be388
-- title:
--   The actual generic source bounds the canonical generic fibre of a cartesian family completion
-- statement:
--   Let $U,N$ be integral schemes, let $p:Y\to U$ be a morphism, and let $b:\operatorname{Spec}E\to U$ be a dominant point valued in a field $E$. Suppose that a given scheme $C$, with its specified maps, is the actual base change
--   $$C\simeq Y\times_U\operatorname{Spec}E.$$
--   Let $V\subset U$ be a dense integral open. Let $W$ be any open subscheme of the restricted family $Y|_V$, and write $p_W:W\to V$ for its structure map. Suppose that $u:V\to N$ is dominant and that an actual cartesian square identifies
--   $$W\simeq G\times_N V$$
--   for a morphism $f:G\to N$.
--
--   For the actual generic point $\eta$ of $N$ one has
--   $$\dim G_\eta\leq\dim C.$$
--   Thus a dimension bound on the prescribed field-base-changed source survives restriction to a dense base open, selection of an open source component, and a cartesian completion over a dominant base map.
--
--   No noetherian, finite-type, properness or smoothness hypothesis is imposed. The schemes $C,Y,W,G$ need not be reduced or integral; the integrality assumptions concern $U,N$ and the chosen base open. The field is unchanged throughout, and all comparisons use the actual cartesian squares and their given maps. The result holds in arbitrary universes and characteristic.
-- source:
--   Auxiliary generic-fibre dimension transport for the Philippon alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 , following the accepted global family model https://prove2.me/theorems/35dae9aa-ba03-4a0c-aea4-045bcc94f746 . The proof uses only Mathlib: factor a field point through the residue field of its image; compare fibres by actual pullbacks; use faithfully flat field extensions and prime-chain lifting for dimension; retain the prescribed generic source under restriction and bound the chosen open subfamily by its embedding into that source.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

theorem AlgebraicGeometry.topologicalKrullDim_genericFiber_le_of_cartesian_open_subfamily
    (E : Type u) [Field E] {Y C U W G N : Scheme.{u}} [IsIntegral U] [IsIntegral N]
    (p : Y ⟶ U) (b : Spec (.of E) ⟶ U) [IsDominant b]
    (e : C ⟶ Y) (p₀ : C ⟶ Spec (.of E)) (hp₀ : IsPullback e p₀ p b)
    (V : U.Opens) [IsIntegral (V : Scheme.{u})] (hdV : Dense (V : Set U))
    (i : W ⟶ (p ⁻¹ᵁ V : Scheme.{u})) [IsOpenImmersion i]
    (t : W ⟶ G) (f : G ⟶ N) (u : (V : Scheme.{u}) ⟶ N) [IsDominant u]
    (hG : IsPullback t (i ≫ (p ∣_ V)) f u)
    (η : N) (hη : IsGenericPoint η Set.univ) :
    topologicalKrullDim (f.fiber η) ≤ topologicalKrullDim C := by sorry
