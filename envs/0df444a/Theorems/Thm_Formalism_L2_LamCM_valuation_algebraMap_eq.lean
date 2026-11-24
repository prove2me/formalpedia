-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_valuation_algebraMap_eq
-- name    : Formalism.L2.LamCM.valuation_algebraMap_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:03.769377+00:00
-- url     : https://prove2.me/theorems/d44a1ec0-b32a-47c9-9624-252f7667b7b6
-- title:
--   Lam CM: valuation algebra Map eq
-- statement:
--   The Lam CM construction uses the valuation algebra Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L38-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L38-L42

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.LamCM.valuation_algebraMap_eq (v : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    v.valuation K (algebraMap (𝓞 K) K r) =
      WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K r))) := by sorry
