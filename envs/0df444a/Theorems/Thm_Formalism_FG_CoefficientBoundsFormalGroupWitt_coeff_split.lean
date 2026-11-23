-- Prove2me | Theorems.Thm_Formalism_FG_CoefficientBoundsFormalGroupWitt_coeff_split
-- name    : Formalism.FG.CoefficientBoundsFormalGroupWitt.coeff_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:49.320481+00:00
-- url     : https://prove2.me/theorems/7a32161a-9e28-4056-9ccc-4e347b7102e0
-- title:
--   Coefficient Bounds Formal Group Witt: coeff split
-- statement:
--   The Coefficient Bounds Formal Group Witt construction uses the coeff split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CoeffV.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CoeffV.lean#L24-L31

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
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
open Formalism Formalism.FG Formalism.FG.CoefficientBoundsFormalGroupWitt
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.FG.CoefficientBoundsFormalGroupWitt.coeff_split {ι : Type v} [Fintype ι] {τ : Type w} (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K)
    (M : ι → ι → K) (f : ι → MvPowerSeries τ K) (j : ι) (n : τ →₀ ℕ) :
    MvPowerSeries.coeff n (f j) = MvPowerSeries.coeff n (f j - (p : K)⁻¹ •
        ∑ k, M j k • MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k))) +
      (p : K)⁻¹ * ∑ k, M j k *
        MvPowerSeries.coeff n (MvPowerSeries.expand q hq (MvPowerSeries.map σ (f k))) := by sorry
