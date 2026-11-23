-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_logy_lt
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.logy_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:52.786893+00:00
-- url     : https://prove2.me/theorems/4992a07c-30ab-41cc-8a25-3c7326fadd22
-- title:
--   Primes In Progressions: logy lt
-- statement:
--   The Primes In Progressions construction uses the logy lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean#L65-L72

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.logy_lt {cA M y : ℝ} (hcA : 0 < cA) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) : cA ^ 2 * Real.log y < Real.log M ^ 2 := by sorry
