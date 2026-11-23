-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_pow_exp_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_pow_exp_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:51.098546+00:00
-- url     : https://prove2.me/theorems/0bc75cbc-8ffc-4cce-95fc-df196fb3e5e9
-- title:
--   Primes In Progressions: dhpr pow exp le
-- statement:
--   The Primes In Progressions construction uses the dhpr pow exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeB.lean#L9-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeB.lean#L9-L21

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHPrimeB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_pow_exp_le (m : ℕ) {b t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) :
    b ^ m * (t ^ m * Real.exp (-(b * t))) ≤ (m.factorial : ℝ) := by sorry
