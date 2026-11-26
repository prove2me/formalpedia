-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_numerator_div_global_le_card_mul_moment
-- name    : CollatzEndpointTransport.FixedTotal.numerator_div_global_le_card_mul_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:47.247438+00:00
-- url     : https://prove2.me/theorems/f65625af-d21a-5e2f-83ae-0abf2d38d441
-- title:
--   Fixed Total: numerator div global le card mul moment
-- statement:
--   The Fixed Total construction uses the numerator div global le card mul moment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L335-L365
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L335-L365

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

theorem CollatzEndpointTransport.FixedTotal.numerator_div_global_le_card_mul_moment
    {N s B : ℕ} {theta : ℝ}
    (htheta : 0 ≤ theta)
    (hcard : 0 < (fixedSet N s).card)
    (hB : (fixedSet N s).card ≤ B) :
    fixedRenyiNumerator N s theta / (B : ℝ) ^ theta ≤
      ((fixedSet N s).card : ℝ) * fixedRenyiMoment N s theta := by sorry
