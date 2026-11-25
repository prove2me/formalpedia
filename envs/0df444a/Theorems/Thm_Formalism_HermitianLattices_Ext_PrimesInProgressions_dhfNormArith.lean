-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhfNormArith
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhfNormArith
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:33:39.32085+00:00
-- url     : https://prove2.me/theorems/df3ef4c3-78ad-5893-b66c-b213678d2d92
-- title:
--   Primes In Progressions: dhf Norm Arith
-- statement:
--   The Primes In Progressions construction uses the dhf Norm Arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHIneqFA.lean#L176-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHIneqFA.lean#L176-L192

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqFA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhfNormArith (D3 D4 P3 P4 S3 S4 I3 I4 A B : ℂ) (k : ℕ) (e3 e4 Dom X : ℝ)
    (h3 : ‖D3 - P3 + S3‖ ≤ e3) (h4 : ‖D4 - P4 + S4‖ ≤ e4)
    (hD3 : D3 = (-1 : ℂ) ^ k / (k.factorial : ℂ) * A) (hD4 : D4 = (-1 : ℂ) ^ k / (k.factorial : ℂ) * B)
    (hdom : ‖A + B‖ ≤ Dom) (hP : ‖P3 + P4 - I3 - I4‖ ≤ X) :
    ‖(S3 - I3) + (S4 - I4)‖ ≤ Dom / (k.factorial : ℝ) + X + e3 + e4 := by sorry
