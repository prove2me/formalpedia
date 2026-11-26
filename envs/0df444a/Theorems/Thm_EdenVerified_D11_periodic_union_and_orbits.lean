-- Prove2me | Theorems.Thm_EdenVerified_D11_periodic_union_and_orbits
-- name    : EdenVerified.D11_periodic_union_and_orbits
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:27:27.473354+00:00
-- url     : https://prove2.me/theorems/fb484f11-694a-454e-954d-ef3599a810e9
-- title:
--   Eden Verified: D11 periodic union and orbits
-- statement:
--   Equilibrium points belong to the positive-return union, and the four nonconstant
--   periodic orbits are four distinct geometric orbit sets.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L675-L691
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L675-L691

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D11_periodic_union_and_orbits (c : ℝ) (hc : 0 < c) :
    periodicEquilibriumSet c = attractor ∩
      ({p : PhaseSpace | vectorField c p = 0} ∪
       {p : PhaseSpace | ∃ τ : ℝ, 0 < τ ∧ evolution c τ p = p}) ∧
    periodicEquilibriumSet c =
      {p : PhaseSpace | p ∈ attractor ∧ ∃ τ : ℝ, 0 < τ ∧ evolution c τ p = p} ∧
    geometricPeriodicOrbits c =
      {O : Set PhaseSpace | ∃ p : PhaseSpace,
        (∃ τ : ℝ, 0 < τ ∧ evolution c τ p = p) ∧ vectorField c p ≠ 0 ∧
        {z : PhaseSpace | ∃ τ : ℝ, 0 ≤ τ ∧ evolution c τ p = z} = O} ∧
    geometricPeriodicOrbits c =
      {firstCircle 1, firstCircle 2, secondCircle 1, secondCircle 2} ∧
    (geometricPeriodicOrbits c).encard = 4 := by sorry
