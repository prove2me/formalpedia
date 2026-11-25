-- Prove2me | Theorems.Thm_Darpa018_GroupExtension_obstruction_zero_iff_of_lifts
-- name    : Darpa018.GroupExtension.obstruction_zero_iff_of_lifts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:31:55.565876+00:00
-- url     : https://prove2.me/theorems/5571186c-cf4d-4677-b1bd-1ac095ff5153
-- title:
--   Group Extension: obstruction zero iff of lifts
-- statement:
--   Vanishing of the obstruction is independent of the chosen pointwise lifts.
--
--   Source: https://github.com/AItoBit/DARPA-s-23-Mathematical-Challenges/blob/42b1d19b3d53ff5333725ef4410c1e0de84b22d2/Solution.lean#L410-L412
-- source:
--   https://github.com/AItoBit/DARPA-s-23-Mathematical-Challenges/blob/42b1d19b3d53ff5333725ef4410c1e0de84b22d2/Solution.lean#L410-L412

module
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Tactic.NoncommRing
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Definitions.Def_DarpaH2Lifting_Solution
set_option autoImplicit false
@[expose] public section
public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Darpa018 Darpa018.GroupExtension
open scoped IsMulCommutative
variable {G E Q : Type} [Group G] [Group E] [Group Q]
variable (q : E →* Q) [IsMulCommutative q.ker]
variable (ρ : G →* Q) (l : G → E) (hl : ∀ g, q (l g) = ρ g)

theorem Darpa018.GroupExtension.obstruction_zero_iff_of_lifts (l' : G → E) (hl' : ∀ g, q (l' g) = ρ g) :
    obstruction q ρ l hl = 0 ↔ obstruction q ρ l' hl' = 0 := by sorry
