-- Prove2me | Theorems.Thm_ContactCalculus_hopf_family_reeb_characterization
-- name    : ContactCalculus.hopf_family_reeb_characterization
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T15:39:52.305262+00:00
-- url     : https://prove2.me/theorems/45b6c5f6-2d8e-4a43-9893-71b4ae8d242c
-- title:
--   Reeb characterization of the weighted Hopf family on the unit sphere
-- statement:
--   For a point y on the unit three-sphere and t >= 0, an ambient vector u is sphere-tangent, has Hopf form value one, and annihilates its exterior derivative on all sphere-tangent vectors if and only if u is the explicit field (-y_1,y_0,-y_3/(1+t),y_2/(1+t)). This verifies existence and uniqueness directly, without an assumed contact-form predicate.
-- source:
--   Geiges, Contact Geometry, https://arxiv.org/pdf/math/0307242, Definition 2.5 and Remark 2.21(1), printed p. 15. Explicit coordinate verification of the displayed Hopf Reeb fields, including uniqueness.

import Definitions.Def_GrayStability_HopfFamily
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
open GrayStability
open scoped ContDiff

theorem ContactCalculus.hopf_family_reeb_characterization (t : ℝ) (ht : 0 ≤ t)
    (y : E 4) (hy : y ∈ levelSet unitSphereEquation) (u : E 4) :
    (u ∈ tangentSpace unitSphereEquation y ∧ hopfFamily t y u = 1 ∧
      ∀ v ∈ tangentSpace unitSphereEquation y,
        extDerivOneForm (hopfFamily t) y u v = 0) ↔
      u = ![-y 1, y 0, -y 3 / (1 + t), y 2 / (1 + t)] := by sorry
