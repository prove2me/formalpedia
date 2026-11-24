-- Prove2me | Theorems.Thm_Formalism_LT_InvIntP_invIntegralOfClass
-- name    : Formalism.LT.InvIntP.invIntegralOfClass
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:55.855796+00:00
-- url     : https://prove2.me/theorems/8c6ff847-aad0-47a2-9cb7-aca3c8e04a16
-- title:
--   Inv Int P: inv Integral Of Class
-- statement:
--   The Inv Int P construction uses the inv Integral Of Class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L181-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/InvInt.lean#L181-L234

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
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
universe u v
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR

theorem Formalism.LT.InvIntP.invIntegralOfClass (K : Type u) [NormedField K] [IsUltrametricDist K] (ι : Type v)
    [Finite ι] (C : MvPowerSeries ι K → Prop) (f : PowerSeries K)
    (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1)
    (hsub : ∀ a b, C a → C b → C (a - b))
    (hP : ∀ P : MvPowerSeries ι K, MvPowerSeries.constantCoeff P = 0 → IntegralMv P →
      C (f.subst P))
    (hlowC : ∀ D, C D → ∀ N : ℕ, 1 ≤ N →
      (∀ d : ι →₀ ℕ, d.degree < N → MvPowerSeries.coeff d D = 0) →
      ∀ d : ι →₀ ℕ, d.degree = N → ‖MvPowerSeries.coeff d D‖ ≤ 1)
    (h : MvPowerSeries ι K) (hh0 : MvPowerSeries.constantCoeff h = 0) (hCh : C (f.subst h)) :
    IntegralMv h := by sorry
