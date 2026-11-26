-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_three_pow_rpow_one_sub_div
-- name    : CollatzEndpointTransport.FixedTotal.three_pow_rpow_one_sub_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:05:56.872007+00:00
-- url     : https://prove2.me/theorems/4e75ff57-31bc-4605-a26a-7b9dceb417f6
-- title:
--   Fixed Total: three pow rpow one sub div
-- statement:
--   The Fixed Total construction uses the three pow rpow one sub div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalNonlinearShell.lean#L29-L51
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalNonlinearShell.lean#L29-L51

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.three_pow_rpow_one_sub_div
    (D : ℝ) (n : ℕ) :
    ((3 : ℝ) ^ n) ^ (1 - D) / (3 : ℝ) ^ n =
      (Real.exp (-D * Real.log 3)) ^ n := by sorry
