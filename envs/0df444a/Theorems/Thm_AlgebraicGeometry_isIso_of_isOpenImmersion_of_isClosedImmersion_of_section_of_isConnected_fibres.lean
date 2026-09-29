-- Prove2me | Theorems.Thm_AlgebraicGeometry_isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres
-- name    : AlgebraicGeometry.isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/fcca3793-e135-5f6c-888a-faa53054f941
-- title:
--   Clopen subscheme containing a section, connected fibres
-- statement:
--   Let $X$, $Y$, $Z$ be schemes and $p : X \to Y$ a morphism of schemes such that for every point $y$ of $Y$ the fibre $p^{-1}(y)$, taken as the preimage of $\{y\}$ under the underlying continuous map of $p$ and regarded as a subspace of the underlying topological space of $X$, is connected (nonempty and preconnected). Let $e : Y \to X$ be a section of $p$, in the sense that $e$ followed by $p$ is the identity of $Y$, and let $\iota : Z \to X$ be a morphism which is simultaneously an open immersion and a closed immersion. Assume further that $e$ factors through $\iota$, i.e. there exists a morphism $e_0 : Y \to Z$ with $e_0$ followed by $\iota$ equal to $e$. Then $\iota$ is an isomorphism of schemes. The proof uses only preconnectedness of the fibres, not their nonemptiness.
--
--   This is the standard clopen-locus principle: a subscheme of $X$ that is open and closed and contains the image of a section of $p$ must be all of $X$, provided the fibres of $p$ are connected. It is applied to rigidified line bundles on abelian schemes, where the locus on which a line bundle becomes trivial is clopen and contains the zero section; it is cited by [`AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_locIsoOnBase_unit_faces_of_isNoetherianRing`](thm.html#AlgebraicGeometry.RelPicard.RigidifiedLineBundle.nonempty_iso_unit_of_locIsoOnBase_unit_faces_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isIso_of_isOpenImmersion_of_isClosedImmersion_of_section_of_isConnected_fibres
    {X Y Z : Scheme} (p : X ⟶ Y) (hconn : ∀ y : Y, _root_.IsConnected (p.base ⁻¹' {y}))
    (e : Y ⟶ X) (he : e ≫ p = 𝟙 Y)
    (ι : Z ⟶ X) [IsOpenImmersion ι] [IsClosedImmersion ι]
    (hZ : ∃ e₀ : Y ⟶ Z, e₀ ≫ ι = e) :
    IsIso ι := by sorry
