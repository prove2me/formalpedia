-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_log_nonneg
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_log_nonneg
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:52:02.454665+00:00
-- url     : https://prove2.me/theorems/adf442ff-94a9-5abc-887e-42a70e0417a7
-- title:
--   Primes In Progressions: exbox log nonneg
-- statement:
--   The Primes In Progressions construction uses the exbox log nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplBox.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplBox.lean#L33-L37

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLocL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplBox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_log_nonneg {M : ℕ} (hM : 3 ≤ M) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ Real.log ((M : ℝ) * (a + 2)) := by sorry
