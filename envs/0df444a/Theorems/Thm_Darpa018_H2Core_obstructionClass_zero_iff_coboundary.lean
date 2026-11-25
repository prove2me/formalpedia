-- Prove2me | Theorems.Thm_Darpa018_H2Core_obstructionClass_zero_iff_coboundary
-- name    : Darpa018.H2Core.obstructionClass_zero_iff_coboundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:31:44.197649+00:00
-- url     : https://prove2.me/theorems/4239cb82-b72d-592b-ad8a-77fdc3ddd979
-- title:
--   H2 Core: obstruction Class zero iff coboundary
-- statement:
--   A cocycle has zero cohomology class exactly when it is a coboundary.
--
--   Source: https://github.com/AItoBit/DARPA-s-23-Mathematical-Challenges/blob/42b1d19b3d53ff5333725ef4410c1e0de84b22d2/Solution.lean#L86-L96
-- source:
--   https://github.com/AItoBit/DARPA-s-23-Mathematical-Challenges/blob/42b1d19b3d53ff5333725ef4410c1e0de84b22d2/Solution.lean#L86-L96

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
open Darpa018 Darpa018.H2Core
variable {G M : Type}
variable [Group G] [AddCommGroup M] [DistribMulAction G M]

theorem Darpa018.H2Core.obstructionClass_zero_iff_coboundary
    (c : G × G → M)
    (hc : groupCohomology.IsCocycle₂ c) :
    obstructionClass c hc = 0 ↔ groupCohomology.IsCoboundary₂ c := by sorry
