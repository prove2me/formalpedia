-- Prove2me | Theorems.Thm_Formalism_LT_Asm_funEqInv
-- name    : Formalism.LT.Asm.funEqInv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:28.90384+00:00
-- url     : https://prove2.me/theorems/b4f4f9ac-696f-449f-a81c-55f0986798d9
-- title:
--   Asm: fun Eq Inv
-- statement:
--   The Asm construction uses the fun Eq Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L66-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/MapSubtypeInjective.lean#L66-L77

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MapSubtypeInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.Asm
open Formalism.G

theorem Formalism.LT.Asm.funEqInv (h2 : InvIntegralOfClass.{u, 0}) (h3 : FunEqLowCoeff.{u, 0})
    (hk : Formalism.G.FunEqSubst.{u, 0})
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {p q : ℕ} {σ : K →+* K}
    (hS : FunctionalEquationSetting K p q σ) {ι : Type} [Finite ι] {f : PowerSeries K}
    (hf0 : constantCoeff f = 0) (hf1 : coeff 1 f = 1) (hfE : IsFunEqType p q σ f)
    (h : MvPowerSeries ι K) (hh0 : MvPowerSeries.constantCoeff h = 0)
    (hC : IsFunEqTypeMv p q (q_ne_zero hS) σ (f.subst h)) : IntegralMv h := by sorry
