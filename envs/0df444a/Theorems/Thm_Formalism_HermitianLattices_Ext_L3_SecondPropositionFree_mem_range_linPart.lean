-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_SecondPropositionFree_mem_range_linPart
-- name    : Formalism.HermitianLattices.Ext.L3.SecondPropositionFree.mem_range_linPart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:05.479557+00:00
-- url     : https://prove2.me/theorems/8d35113b-741c-424d-b8d1-0f931e557348
-- title:
--   Second Proposition Free: mem range lin Part
-- statement:
--   The Second Proposition Free construction uses the mem range lin Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemRangeLinPart.lean#L168-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemRangeLinPart.lean#L168-L183

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemRangeLinPart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.SecondPropositionFree
open NormLifting
variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}

theorem Formalism.HermitianLattices.Ext.L3.SecondPropositionFree.mem_range_linPart (I : Ideal A) {M : ℕ} (y : Fin M → A) (i₀ : Fin M)
    {b : A} (hb : σ (y i₀) * b + σ b * y i₀ = 1) {w : A} (hw : w ∈ fixSub σ I) :
    w ∈ (linPart σ I y).range := by sorry
