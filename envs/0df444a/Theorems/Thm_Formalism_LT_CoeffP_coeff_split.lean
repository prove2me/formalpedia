-- Prove2me | Theorems.Thm_Formalism_LT_CoeffP_coeff_split
-- name    : Formalism.LT.CoeffP.coeff_split
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:42.37853+00:00
-- url     : https://prove2.me/theorems/9da1f1fb-ef95-46f3-9d20-3d26f4b69a37
-- title:
--   Coeff P: coeff split
-- statement:
--   The Coeff P construction uses the coeff split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/SigmaNormLeOne.lean#L27-L32

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
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
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.LT.CoeffP.coeff_split (p q : ℕ) (hq : q ≠ 0) (σ : K →+* K) (f : PowerSeries K) (n : ℕ) :
    coeff n f = coeff n (f - (p : K)⁻¹ • (PowerSeries.map σ f).subst
        ((PowerSeries.X : PowerSeries K) ^ q)) +
      (p : K)⁻¹ * (if q ∣ n then σ (coeff (n / q) f) else 0) := by sorry
