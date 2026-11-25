-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_Hyp_abel_identity
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.abel_identity
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:34:05.326477+00:00
-- url     : https://prove2.me/theorems/b3079d5e-59a9-5aeb-8d0f-038ef2374884
-- title:
--   Hyp: abel identity
-- statement:
--   The Hyp construction uses the abel identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperB.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHHyperB.lean#L32-L43

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperB
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.abel_identity (c : ℕ → ℂ) (w : ℕ → ℝ) (U : ℕ) : ∀ V, U ≤ V →
    ∑ n ∈ Ioc U V, c n * (w n : ℂ) =
      (∑ n ∈ Ioc 0 V, c n) * (w (V + 1) : ℂ) - (∑ n ∈ Ioc 0 U, c n) * (w (U + 1) : ℂ) +
        ∑ n ∈ Ioc U V, (∑ k ∈ Ioc 0 n, c k) * ((w n - w (n + 1) : ℝ) : ℂ) := by sorry
