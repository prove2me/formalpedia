-- Prove2me | Theorems.Thm_Formalism_LT_ExpP_term_bound
-- name    : Formalism.LT.ExpP.term_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:56:58.071612+00:00
-- url     : https://prove2.me/theorems/96290a87-90ae-4111-bf8e-f939cf9a709c
-- title:
--   Exp P: term bound
-- statement:
--   The Exp P construction uses the term bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L141-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/NormNatCastOfNotDvd.lean#L141-L163

import Definitions.Def_Formalism_TorsionNormIteration_Statement
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_NormNatCastOfNotDvd
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
open Formalism Formalism.LT Formalism.LT.ExpP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.ExpP.term_bound {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : K)‖ < 1) (z : PowerSeries K)
    (hdz : IntegralPS (PowerSeries.derivative K z)) (d : ℕ) (e : Fin 2 →₀ ℕ) :
    ‖coeff d z • MvPowerSeries.coeff e
      (((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) + (p : K) • MvPowerSeries.X 1) ^ d -
        MvPowerSeries.X 0 ^ d)‖ ≤
        ‖(p : K)‖ := by sorry
