-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_central_cohort_normalized_le
-- name    : CollatzEndpointTransport.FixedTotal.central_cohort_normalized_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:03:55.498407+00:00
-- url     : https://prove2.me/theorems/92ef40da-1a53-41d2-8da2-60e7d322f388
-- title:
--   Fixed Total: central cohort normalized le
-- statement:
--   One central cohort after normalization by the complete odd-count level.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L368-L413
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L368-L413

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralShellCompositionDecidableEq
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralRenyiAdmissibleDecidable

theorem CollatzEndpointTransport.FixedTotal.central_cohort_normalized_le
    {M s : ℕ} {theta eta : ℝ} (u : Fin M)
    (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (((3 : ℝ) ^ s) ^ theta /
        (((sourceOddLevel M s).card : ℝ) ^ theta)) *
      (∑ c ∈ centralLevelCohortSet M s theta eta u,
        ((mapFiberCardAt
          (centralLevelCohortSet M s theta eta u)
          (cohortEndpoint u) c : ℕ) : ℝ) ^ theta) ≤
    if CentralRenyiAdmissible (M - (u : ℕ)) s theta eta then
      ((fixedSet (M - (u : ℕ)) s).card : ℝ) *
        fixedRenyiMoment (M - (u : ℕ)) s theta
    else 0 := by sorry
