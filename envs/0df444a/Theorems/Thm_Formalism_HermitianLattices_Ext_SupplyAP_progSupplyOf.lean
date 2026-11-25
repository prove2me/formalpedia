-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_progSupplyOf
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.progSupplyOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:00:45.393088+00:00
-- url     : https://prove2.me/theorems/914ad3bd-650c-48a3-a8a9-0beb09139757
-- title:
--   Supply AP: prog Supply Of
-- statement:
--   The Supply AP construction uses the prog Supply Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffFinal.lean#L13-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffFinal.lean#L13-L31

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffPsi
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffConsts
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffExc
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_PsiAPLeCount
import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffFinal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.ZeroFreeDirichlet
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP

theorem Formalism.HermitianLattices.Ext.SupplyAP.progSupplyOf (A : ℕ) (hA : ExcBoundAt A) : ∃ K : ℝ, 4 ≤ K ∧ ∀ (m a : ℕ) (x : ℝ), 1 ≤ m → Nat.Coprime a m →
    K * Real.log (3 * m) ^ 2 ≤ Real.log x → Real.sqrt x ≤ ((primesAP m a x).card : ℝ) := by sorry
