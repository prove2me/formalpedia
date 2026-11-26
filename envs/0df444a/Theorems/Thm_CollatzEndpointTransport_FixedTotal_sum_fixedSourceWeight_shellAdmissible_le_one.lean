-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_fixedSourceWeight_shellAdmissible_le_one
-- name    : CollatzEndpointTransport.FixedTotal.sum_fixedSourceWeight_shellAdmissible_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:57.879796+00:00
-- url     : https://prove2.me/theorems/b90b3413-163c-5e02-bafc-5c960f4a5435
-- title:
--   Fixed Total: sum fixed Source Weight shell Admissible le one
-- statement:
--   The Fixed Total construction uses the sum fixed Source Weight shell Admissible le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L603-L637
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/SharpCentralRenyiPullback.lean#L603-L637

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.sum_fixedSourceWeight_shellAdmissible_le_one
    {M N : ℕ} (hN : 0 < N) (theta eta : ℝ) :
    ∑ s ∈ shellAdmissibleLengthSet M N theta eta,
        fixedSourceWeight N s ≤ 1 := by sorry
