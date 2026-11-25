-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhFam_re
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhFam_re
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:24:55.324815+00:00
-- url     : https://prove2.me/theorems/8d7699f2-06a5-5b87-b1ae-cde5c5676809
-- title:
--   Primes In Progressions: dh Fam re
-- statement:
--   The Primes In Progressions construction uses the dh Fam re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHIneqB.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHIneqB.lean#L116-L122

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhFam_re (Z : Finset ℂ) (m : ℂ → ℕ) (s x : ℂ) (η : ℝ) (hZ : ∀ ρ ∈ Z, ρ.re < 1)
    (hs : s.re = 1 + η) (hx : x ∈ dhFam Z m s) : η ≤ x.re := by sorry
