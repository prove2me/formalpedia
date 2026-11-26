-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_levelCriticalFactor_eq
-- name    : CollatzEndpointTransport.FixedTotal.levelCriticalFactor_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:10.665225+00:00
-- url     : https://prove2.me/theorems/369620a2-eeb2-56bc-8a5d-86364c8ea414
-- title:
--   Fixed Total: level Critical Factor eq
-- statement:
--   The Fixed Total construction uses the level Critical Factor eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalNonlinearShell.lean#L53-L73
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalNonlinearShell.lean#L53-L73

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.levelCriticalFactor_eq
    (M s : ℕ) (hs : s ≤ M) :
    Real.sqrt
          ((3 : ℝ) ^ (s + 1) /
            (sourceOddLevel M s).card) *
        (∑ y ∈ actualLevelEndpointSet M s,
          (actualLevelFiberCard M s y : ℝ) *
            Real.sqrt (actualLevelFiberCard M s y)) =
      Real.sqrt 3 * actualLevelCriticalContribution M s := by sorry
