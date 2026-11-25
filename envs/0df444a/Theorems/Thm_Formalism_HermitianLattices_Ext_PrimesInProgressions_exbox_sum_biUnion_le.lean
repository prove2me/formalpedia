-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exbox_sum_biUnion_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_sum_biUnion_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:37:00.706879+00:00
-- url     : https://prove2.me/theorems/75200a3d-d6fe-5a31-af03-229300f81bb8
-- title:
--   Primes In Progressions: exbox sum bi Union le
-- statement:
--   The Primes In Progressions construction uses the exbox sum bi Union le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplBox.lean#L39-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplBox.lean#L39-L46

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_sum_biUnion_le {ι : Type*} (s : Finset ι) (f : ι → Finset ℂ) (w : ℂ → ℕ) :
    ∑ x ∈ s.biUnion f, w x ≤ ∑ i ∈ s, ∑ x ∈ f i, w x := by sorry
