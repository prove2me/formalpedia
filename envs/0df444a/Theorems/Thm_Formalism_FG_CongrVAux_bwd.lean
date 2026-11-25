-- Prove2me | Theorems.Thm_Formalism_FG_CongrVAux_bwd
-- name    : Formalism.FG.CongrVAux.bwd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:54.469004+00:00
-- url     : https://prove2.me/theorems/e249f939-d9ff-4adc-9c3d-3af90e0e2ed4
-- title:
--   Congr VAux: bwd
-- statement:
--   The Congr VAux construction uses the bwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L216-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CongrV.lean#L216-L292

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}

theorem Formalism.FG.CongrVAux.bwd [CharZero K] {p q : ℕ} {hq : q ≠ 0} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ)
    {ι : Type v} [Fintype ι] [DecidableEq ι] {M : ι → ι → K} (hM : IntegralMat M)
    {f : ι → MvPowerSeries ι K} (hf : IsIdMod2 f) (hfe : IsFunEqTypeV p q hq σ M f)
    {α β : ι → MvPowerSeries τ K} (hα0 : ∀ i, constantCoeff (α i) = 0)
    (hβ0 : ∀ i, constantCoeff (β i) = 0) (hα : ∀ i, IntegralMv (α i)) (hβ : ∀ i, IntegralMv (β i))
    {r : ℕ} (hr : 1 ≤ r) (hd : ∀ j, DivByMv ((p : K) ^ r) (subst α (f j) - subst β (f j))) :
    ∀ i, DivByMv ((p : K) ^ r) (α i - β i) := by sorry
