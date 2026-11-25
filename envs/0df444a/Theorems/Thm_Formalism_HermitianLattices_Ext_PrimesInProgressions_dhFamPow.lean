-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhFamPow
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhFamPow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:27:25.126057+00:00
-- url     : https://prove2.me/theorems/55150082-8168-4afd-95df-85b2378e9e50
-- title:
--   Primes In Progressions: dh Fam Pow
-- statement:
--   The Primes In Progressions construction uses the dh Fam Pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHIneqB.lean#L130-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHIneqB.lean#L130-L136

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhFamPow (Z : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (k : ℕ) :
    ((dhFam Z m s).map (fun x => 1 / x ^ (k + 1))).sum = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1) := by sorry
