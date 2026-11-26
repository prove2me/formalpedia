-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_orbit_lower_of_parityCorrection
-- name    : CollatzEndpointTransport.Terras.orbit_lower_of_parityCorrection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:28.8245+00:00
-- url     : https://prove2.me/theorems/6c5f5e46-6e1c-427d-8bc0-2cd302b2c6cf
-- title:
--   Terras: orbit lower of parity Correction
-- statement:
--   The lower orbit envelope follows from a lower parity bound and the phase
--   budget `3^(eta*k) ≤ n^t`.  The correction is nonnegative and therefore helps
--   the lower bound.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean#L102-L151
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean#L102-L151

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real

theorem CollatzEndpointTransport.Terras.orbit_lower_of_parityCorrection
    {n k : ℕ} {eta t : ℝ}
    (hn : 0 < n)
    (hS :
      (k : ℝ) / 2 - eta * k ≤ (oddCount k n : ℝ))
    (hphase :
      (3 : ℝ) ^ (eta * k) ≤ (n : ℝ) ^ t) :
    centralOrbitScale k * (n : ℝ) ^ (1 - t) ≤
      ((T^[k]) n : ℝ) := by sorry
