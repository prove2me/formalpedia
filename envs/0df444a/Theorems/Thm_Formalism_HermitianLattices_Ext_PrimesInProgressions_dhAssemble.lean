-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhAssemble
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhAssemble
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:24:49.599733+00:00
-- url     : https://prove2.me/theorems/5f52174c-4eb3-536b-8036-c06e4160801f
-- title:
--   Primes In Progressions: dh Assemble
-- statement:
--   The Primes In Progressions construction uses the dh Assemble property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHIneqB.lean#L94-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHIneqB.lean#L94-L114

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhAssemble {β : Type*} [AddCommGroup β] (F1 F2 F3 F4 : Multiset ℂ) (b2 b3 b4 : ℂ)
    (c3 c4 : Prop) [Decidable c3] [Decidable c4] (h2 : b2 ∈ F2) (h3 : c3 → b3 ∈ F3) (h4 : c4 → b4 ∈ F4)
    (g : ℂ → β) :
    ((F1 + F2.erase b2 + (if c3 then F3.erase b3 else F3) + (if c4 then F4.erase b4 else F4)).map g).sum
      = (F1.map g).sum + (F2.map g).sum + (F3.map g).sum + (F4.map g).sum - g b2
        - (if c3 then g b3 else 0) - (if c4 then g b4 else 0) := by sorry
