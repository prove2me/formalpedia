-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_etaOf_far
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.etaOf_far
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:18:20.500048+00:00
-- url     : https://prove2.me/theorems/96ddf7af-60ea-4873-a944-3fcee6898e29
-- title:
--   Primes In Progressions: eta Of far
-- statement:
--   The Primes In Progressions construction uses the eta Of far property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean#L169-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean#L169-L186

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.etaOf_far (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ)
    (h : eOf M = some (χ₁, β₁)) (hr : ¬ InRegion cZ M (β₁ : ℂ)) : cZ / 2 ≤ etaOf M := by sorry
