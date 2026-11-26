-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fiber_le_ordinary_add_critical
-- name    : CollatzEndpointTransport.FixedTotal.fiber_le_ordinary_add_critical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:59.656932+00:00
-- url     : https://prove2.me/theorems/50bdc1ec-bd49-4cd5-9347-2b1a30ef704b
-- title:
--   Fixed Total: fiber le ordinary add critical
-- statement:
--   Pointwise heavy/ordinary split at reference size `R` and total mass
--   `N`.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFiberSplit.lean#L28-L64
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFiberSplit.lean#L28-L64

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalEndpointTarget
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFiberSplit
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fiber_le_ordinary_add_critical
    {E N R f : ℝ}
    (hE : 0 < E) (hN : 0 < N) (hR : 0 < R) (hf : 0 ≤ f) :
    f ≤
      E ^ 2 * N / R +
        E⁻¹ * Real.sqrt (R / N) * f * Real.sqrt f := by sorry
