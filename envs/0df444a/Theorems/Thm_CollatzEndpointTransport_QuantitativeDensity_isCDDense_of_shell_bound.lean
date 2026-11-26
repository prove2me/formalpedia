-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_isCDDense_of_shell_bound
-- name    : CollatzEndpointTransport.QuantitativeDensity.isCDDense_of_shell_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:10:08.703705+00:00
-- url     : https://prove2.me/theorems/d5aa6a75-5b8b-5d8f-8cec-0b7112f0c02f
-- title:
--   Quantitative Density: is CDDense of shell bound
-- statement:
--   **Shell-to-global density transport.**
--
--   If the exceptional fraction of every dyadic shell is at most
--   `K * exp (-c * M)`, and the shell rate `c` is below `log 2`, then the
--   exceptional set is `(C,D)`-dense-complemented with
--
--     D = c / log 2,      C = 2 K / (2 * exp (-c) - 1).
--
--   The constant is explicit and the geometric series is summed exactly; no
--   asymptotic step occurs.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/ShellToGlobalDensity.lean#L88-L182
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/ShellToGlobalDensity.lean#L88-L182

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensity
import Definitions.Def_CollatzEndpointTransport_Common_ShellToGlobalDensity
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.QuantitativeDensity.isCDDense_of_shell_bound
    {S : Set ℕ} {K c : ℝ}
    (hK : 0 < K) (hc : 0 < c) (hclt : c < Real.log 2)
    (hshell : ∀ M : ℕ,
      ((shellBad S M).card : ℝ) ≤ K * Real.exp (-c * M) * 2 ^ M) :
    IsCDDense S (2 * K / (2 * Real.exp (-c) - 1)) (c / Real.log 2) := by sorry
