-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_orbit_upper_of_parityCorrection
-- name    : CollatzEndpointTransport.Terras.orbit_upper_of_parityCorrection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:21:32.725458+00:00
-- url     : https://prove2.me/theorems/92b6825b-d9b4-5edf-b84d-256cb851bfa2
-- title:
--   Terras: orbit upper of parity Correction
-- statement:
--   The upper orbit envelope.  The target is split equally between the
--   multiplicative main term and the affine correction.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean#L155-L223
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean#L155-L223

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
import Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real

theorem CollatzEndpointTransport.Terras.orbit_upper_of_parityCorrection
    {n k : ℕ} {eta t : ℝ}
    (hn : 0 < n)
    (hS :
      (oddCount k n : ℝ) ≤ (k : ℝ) / 2 + eta * k)
    (hphase :
      2 * (3 : ℝ) ^ (eta * k) ≤ (n : ℝ) ^ t)
    (hcorr :
      affineCorrection k n * (3 : ℝ) ^ ((k : ℝ) / 2) ≤
        (n : ℝ) ^ eta)
    (hcorrAbsorb :
      2 * ((n : ℝ) ^ eta * (3 : ℝ) ^ (eta * k)) ≤
        centralOrbitScale k * (n : ℝ) ^ (1 + t)) :
    ((T^[k]) n : ℝ) ≤
      centralOrbitScale k * (n : ℝ) ^ (1 + t) := by sorry
