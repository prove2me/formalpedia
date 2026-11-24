-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_supplyPrimesOf
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.supplyPrimesOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:28.311353+00:00
-- url     : https://prove2.me/theorems/eae32eaa-68e5-4d23-ac3e-309b18b3f2b3
-- title:
--   Supply AP: supply Primes Of
-- statement:
--   The Supply AP construction uses the supply Primes Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffFinal.lean#L33-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffFinal.lean#L33-L74

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

theorem Formalism.HermitianLattices.Ext.SupplyAP.supplyPrimesOf (A : ℕ) (hA : ExcBoundAt A) : ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 1 ≤ m → ∃ S : Finset ℕ, S.card = n ∧
    ∀ q ∈ S, q.Prime ∧ q ≡ 1 [MOD m] ∧ (q : ℝ) ≤ Real.exp (C * Real.log (2 * m * (n + 2)) ^ 2) := by sorry
