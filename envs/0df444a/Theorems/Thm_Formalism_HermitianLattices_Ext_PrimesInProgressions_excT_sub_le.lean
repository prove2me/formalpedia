-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_excT_sub_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.excT_sub_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:15:41.375352+00:00
-- url     : https://prove2.me/theorems/94bbac66-e2f7-5570-b74d-7f59b286d7b6
-- title:
--   Primes In Progressions: exc T sub le
-- statement:
--   The Primes In Progressions construction uses the exc T sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmB.lean#L68-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmB.lean#L68-L108

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmB
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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.excT_sub_le {M : ℕ} [NeZero M] (hM : 3 ≤ M) (e : Option (DirichletCharacter ℂ M × ℝ))
    (he : ∀ p, e = some p → IsExcPair p.1 p.2) (χ : DirichletCharacter ℂ M)
    (Z : Finset ℂ) (y κ T : ℝ) (hy : 1 ≤ y) (hT : 0 ≤ T)
    (hZ : ∀ ρ : ℂ, IsLZero χ ρ → 1 - κ / 2 ≤ ρ.re → |ρ.im| ≤ T → ρ ∈ Z) :
    ‖excT e χ y - ∑ ρ ∈ Z, (excW e χ ρ : ℂ) * (y : ℂ) ^ ρ / ρ‖ ≤ excI e χ * (2 * y * y ^ (-(κ / 2))) := by sorry
