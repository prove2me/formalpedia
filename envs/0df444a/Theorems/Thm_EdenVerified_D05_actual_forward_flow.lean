-- Prove2me | Theorems.Thm_EdenVerified_D05_actual_forward_flow
-- name    : EdenVerified.D05_actual_forward_flow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:26:13.782678+00:00
-- url     : https://prove2.me/theorems/b7439032-0d23-57c8-bc5d-299805cdd500
-- title:
--   Eden Verified: D05 actual forward flow
-- statement:
--   Global forward solutions, uniqueness and the evolution law.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L546-L560
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L546-L560

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D05_actual_forward_flow (c : ℝ) :
    (∀ p : PhaseSpace, evolution c 0 p = p ∧
      ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun τ => evolution c τ p)
        (vectorField c (evolution c t p)) t) ∧
    (∀ (p : PhaseSpace) (f : ℝ → PhaseSpace),
      ContinuousOn f (Ici 0) →
      (∀ t : ℝ, 0 ≤ t → HasDerivWithinAt f (vectorField c (f t)) (Ici t) t) →
      f 0 = p → EqOn f (fun t => evolution c t p) (Ici 0)) ∧
    (∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ p : PhaseSpace,
      evolution c (s + t) p = evolution c t (evolution c s p)) ∧
    (∀ (t : ℝ), 0 ≤ t → ∀ n : WithTop ℕ∞, ContDiff ℝ n (evolution c t)) := by sorry
