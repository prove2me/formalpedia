-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
-- name    : CollatzEndpointTransport.FixedTotal.card_sourceOddLevel
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:58:25.908855+00:00
-- url     : https://prove2.me/theorems/db01f55e-7d92-4684-bd13-636f84c2da9a
-- title:
--   Fixed Total: card source Odd Level
-- statement:
--   The exact binomial cardinality of a source-code odd-count level.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalOddCountMGF.lean#L49-L80
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalOddCountMGF.lean#L49-L80

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalShellCoding
import Mathlib.Data.Nat.Choose.Sum
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalOddCountMGF
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.card_sourceOddLevel
    (M s : ℕ) :
    (sourceOddLevel M s).card = M.choose s := by sorry
