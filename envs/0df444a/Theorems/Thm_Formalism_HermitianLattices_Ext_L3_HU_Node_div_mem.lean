-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Node_div_mem
-- name    : Formalism.HermitianLattices.Ext.L3.HU.Node.div_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:49:25.138061+00:00
-- url     : https://prove2.me/theorems/7d7a6937-7379-4d20-bc9f-35b81719b0a0
-- title:
--   Node: div mem
-- statement:
--   The Node construction uses the div mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/PolNatDegreeLe.lean#L12-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/PolNatDegreeLe.lean#L12-L34

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLocUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_PolNatDegreeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
variable {K : Type*} [Field K] [StarRing K] {S : Subring K} {ϖ : K}
variable {n : Type*} [Fintype n] [DecidableEq n]
open Formalism.HermitianLattices.Ext.L3.HU.Node

theorem Formalism.HermitianLattices.Ext.L3.HU.Node.div_mem (hS : IsLocUnif S ϖ) : ∀ (l : ℕ) (f : K), f ∈ S → star f = f →
    f * (ϖ⁻¹) ^ (l + 1) ∉ S → ϖ ^ l * f⁻¹ ∈ S := by sorry
