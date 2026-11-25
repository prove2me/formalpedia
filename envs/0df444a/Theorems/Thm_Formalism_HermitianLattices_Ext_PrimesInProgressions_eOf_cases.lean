-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_eOf_cases
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.eOf_cases
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T06:29:33.984604+00:00
-- url     : https://prove2.me/theorems/6c6d80a7-f949-4451-b08c-38522fa1ba65
-- title:
--   Primes In Progressions: e Of cases
-- statement:
--   The Primes In Progressions construction uses the e Of cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean#L36-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTEOf.lean#L36-L45

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.eOf_cases (M : ℕ) [NeZero M] :
    (∃ p : DirichletCharacter ℂ M × ℝ, eOf M = some p ∧ IsExcPair p.1 p.2 ∧ InRegion cZ M (p.2 : ℂ)) ∨
    (∃ p : DirichletCharacter ℂ M × ℝ, eOf M = some p ∧ IsExcPair p.1 p.2 ∧
      ∀ p' : DirichletCharacter ℂ M × ℝ, IsExcPair p'.1 p'.2 → ¬ InRegion cZ M (p'.2 : ℂ)) ∨
    (eOf M = none ∧ ∀ p' : DirichletCharacter ℂ M × ℝ, ¬ IsExcPair p'.1 p'.2) := by sorry
