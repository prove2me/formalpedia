-- Prove2me | Theorems.Thm_CollatzEndpointTransport_QuantitativeDensity_mem_coneCore_iff_of_mem_three_shell
-- name    : CollatzEndpointTransport.QuantitativeDensity.mem_coneCore_iff_of_mem_three_shell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:32.821439+00:00
-- url     : https://prove2.me/theorems/8fd7eb1c-acf1-51d3-baab-1f4537095bc0
-- title:
--   Quantitative Density: mem cone Core iff of mem three shell
-- statement:
--   On a base-3 shell, the global nested-floor cone is exactly the
--   shell-local cone condition.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativePullbackDefs.lean#L83-L92
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/QuantitativePullbackDefs.lean#L83-L92

import Definitions.Def_CollatzEndpointTransport_Common_AffineCorrectionDensity
import Definitions.Def_CollatzEndpointTransport_Common_TerrasInitialWindow
import Definitions.Def_CollatzEndpointTransport_Common_QuantitativePullbackDefs
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.QuantitativeDensity
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.QuantitativeDensity.mem_coneCore_iff_of_mem_three_shell
    {K j n : ℕ} {eta : ℝ} {S : Set ℕ}
    (hn : 3 ^ j ≤ n ∧ n < 3 ^ (j + 1)) :
    n ∈ coneCore K eta S ↔
      0 < n ∧
      ∀ k : ℕ, (k : ℝ) ≤ eta * j →
        ∀ i : ℕ, i < K * 3 ^ k → 3 ^ k * n + i ∈ S := by sorry
