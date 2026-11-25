-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_log_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_log_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:55:37.440808+00:00
-- url     : https://prove2.me/theorems/18383010-f7fa-46dd-96c7-fbd12d599952
-- title:
--   Primes In Progressions: exbox log le
-- statement:
--   The Primes In Progressions construction uses the exbox log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplBox.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplBox.lean#L23-L31

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_log_le {M : ℕ} (hM : 3 ≤ M) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a + 1) :
    Real.log ((M : ℝ) * (b + 2)) ≤ 2 * Real.log ((M : ℝ) * (a + 2)) := by sorry
