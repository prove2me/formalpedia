-- Prove2me | Theorems.Thm_AlgebraicGeometry_isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed
-- name    : AlgebraicGeometry.isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/764da8fe-ce81-5247-a0d6-90f97226c1c6
-- title:
--   Geometrically connected fibres are connected
-- statement:
--   Let $X$ and $Y$ be schemes (in a fixed universe $u$) and let $f \colon X \to Y$ be a morphism of schemes. Assume that for every type $k$ in the universe $u$ carrying the structure of an algebraically closed field and every morphism of schemes $s \colon \operatorname{Spec} k \to Y$, the underlying topological space of the fibre product $X \times_Y \operatorname{Spec} k$ (Mathlib's categorical pullback of $f$ and $s$ in the category of schemes) is a connected space, i.e. is non-empty and cannot be split into two disjoint non-empty open sets. Then for every point $y$ of the underlying topological space of $Y$ the subset $f^{-1}(\{y\}) \subseteq X$, the preimage of the singleton $\{y\}$ under the continuous map on underlying spaces induced by $f$, is connected in the sense of `IsConnected`: it is non-empty and preconnected. Note that non-emptiness of all geometric fibres is part of the hypothesis and non-emptiness of the topological fibre is part of the conclusion.
--
--   This is the standard implication that geometric connectedness of the fibres of a morphism of schemes forces connectedness (and non-emptiness) of its set-theoretic fibres, as in EGA IV₂ 4.5.13. It is used in the construction of fake elliptic curves and their level structures in the Čerednik–Drinfeld part of the development, where a hypothesis known on all geometric fibres of an auxiliary morphism must be converted into a statement about the fibres over individual points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Y), ConnectedSpace ↥(Limits.pullback f s))
    (y : ↥Y) : _root_.IsConnected (f.base ⁻¹' {y}) := by sorry
