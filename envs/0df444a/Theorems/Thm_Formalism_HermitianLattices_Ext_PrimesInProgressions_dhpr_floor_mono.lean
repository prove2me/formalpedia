-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhpr_floor_mono
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_floor_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:50.876298+00:00
-- url     : https://prove2.me/theorems/01c109a9-a6cd-425d-8c19-3f704e6f82ce
-- title:
--   Primes In Progressions: dhpr floor mono
-- statement:
--   The Primes In Progressions construction uses the dhpr floor mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeB.lean#L208-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHPrimeB.lean#L208-L210

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.dhpr_floor_mono {v w : ℕ} (h : v ≤ w) :
    ⌊Real.exp (v : ℝ)⌋₊ ≤ ⌊Real.exp (w : ℝ)⌋₊ := by sorry
