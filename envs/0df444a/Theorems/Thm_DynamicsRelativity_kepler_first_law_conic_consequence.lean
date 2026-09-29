-- Prove2me | Theorems.Thm_DynamicsRelativity_kepler_first_law_conic_consequence
-- name    : DynamicsRelativity.kepler_first_law_conic_consequence
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-22T23:34:45.438058+00:00
-- url     : https://prove2.me/theorems/01570b89-a3b0-41c8-bc69-5027621b8c6f
-- title:
--   Kepler orbit conic and eccentricity bound implies ellipse trajectory
-- statement:
--   Under an attractive inverse-square Kepler central force field ($k > 0$) with non-zero initial angular momentum ($L(0) \neq 0$) and negative initial energy ($E(0) < 0$), the planetary trajectory $x(t)$ is confined to an ellipse $S$ with the Sun (origin) at one focus.
-- source:
--   David Tong, Dynamics and Relativity, University of Cambridge Part IA Mathematical Tripos lecture notes, Lent 2013, §4.3.1–§4.3.2, pp. 56–60.

import Definitions.Def_DynamicsRelativity_CentralForces_Defs
import Mathlib

open DynamicsRelativity

theorem DynamicsRelativity.kepler_first_law_conic_consequence {k m : ℝ} {x : ℝ → Vec} (hk : 0 < k) (h : KeplerMotion k m x) (hL : angularMomentum m x 0 ≠ 0) (hE : keplerEnergy k m x 0 < 0) : ∃ S : Set Vec, IsEllipseWithFocusAtOrigin S ∧ ∀ t, x t ∈ S := by sorry
