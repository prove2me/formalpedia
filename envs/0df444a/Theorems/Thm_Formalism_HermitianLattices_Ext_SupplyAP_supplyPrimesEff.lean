-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_supplyPrimesEff
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.supplyPrimesEff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:15:33.367299+00:00
-- url     : https://prove2.me/theorems/f7e76340-d3f7-4863-b769-1892aa3fd777
-- title:
--   Supply AP: supply Primes Eff
-- statement:
--   The Supply AP construction uses the supply Primes Eff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffFinal.lean#L76-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffFinal.lean#L76-L78

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

theorem Formalism.HermitianLattices.Ext.SupplyAP.supplyPrimesEff : ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 1 ≤ m → ∃ S : Finset ℕ, S.card = n ∧
    ∀ q ∈ S, q.Prime ∧ q ≡ 1 [MOD m] ∧ (q : ℝ) ≤ Real.exp (C * Real.log (2 * m * (n + 2)) ^ 2) := by sorry
