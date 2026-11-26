-- Prove2me | Theorems.Thm_CollatzEndpointTransport_Terras_log_two_eq_of_mem_dyadicShell
-- name    : CollatzEndpointTransport.Terras.log_two_eq_of_mem_dyadicShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:10:39.722805+00:00
-- url     : https://prove2.me/theorems/02aab411-adb6-4fe9-9c46-821e3896baae
-- title:
--   Terras: log two eq of mem dyadic Shell
-- statement:
--   The dyadic scale of every member of shell `M` is exactly `M`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrectionDensity.lean#L35-L39
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/AffineCorrectionDensity.lean#L35-L39

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrection
import Definitions.Def_CollatzEndpointTransport_Common_ShellToGlobalDensity
import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.Terras.log_two_eq_of_mem_dyadicShell
    {n M : ℕ} (hn : n ∈ QuantitativeDensity.dyadicShell M) :
    Nat.log 2 n = M := by sorry
