-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_SupplyAP_charSum_lowerOf
-- name    : Formalism.HermitianLattices.Ext.SupplyAP.charSum_lowerOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:45.115644+00:00
-- url     : https://prove2.me/theorems/28250098-0bfa-48f0-b61a-192bbd0f72d8
-- title:
--   Supply AP: char Sum lower Of
-- statement:
--   The Supply AP construction uses the char Sum lower Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffPsi.lean#L11-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExceptionalCharacterBounds/EffPsi.lean#L11-L60

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_ExcTerm
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffPsi
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

theorem Formalism.HermitianLattices.Ext.SupplyAP.charSum_lowerOf (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x K : ℝ) (hx : 0 ≤ x)
    (B : DirichletCharacter ℂ q → Finset ℝ) (hB : ∀ χ, ∀ β ∈ B χ, 0 ≤ β)
    (hE : ∀ χ, ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0) +
      ∑ β ∈ B χ, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ K) :
    x - ∑ χ : DirichletCharacter ℂ q, ∑ β ∈ B χ, x ^ β / β - (q.totient : ℝ) * K ≤
      (q.totient : ℝ) * psiAP q a x := by sorry
