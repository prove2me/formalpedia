-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OneGauss_sum_frA_row
-- name    : Formalism.DworkPowerSeriesWeights.OneGauss.sum_frA_row
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:55:15.722322+00:00
-- url     : https://prove2.me/theorems/20cac4a8-b6ef-4192-9922-f678bdc7ebe6
-- title:
--   One Gauss: sum fr A row
-- statement:
--   The One Gauss construction uses the sum fr A row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L136-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneGauss.lean#L136-L145

import Definitions.Def_Formalism_GaussJetBounds_StatementU
import Definitions.Def_Formalism_GaussJetBounds_OneLetterRadius
import Definitions.Def_Formalism_GaussJetBounds_MonoShapeTop
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_GField
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Transfer
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_FJEval
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Labels
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OneGauss

theorem Formalism.DworkPowerSeriesWeights.OneGauss.sum_frA_row {K : Type} [Field K] {N0 N1 : ℕ} (Y : Fin N0 × Fin N0 → K) (i : Fin N0)
    (b : Fin N1) :
    (∑ j : Fin N0 × Fin N1, MvPolynomial.C (frA Y (i, b) j) * MvPolynomial.X j :
      MvPolynomial (Fin N0 × Fin N1) K) =
      ∑ a : Fin N0, MvPolynomial.C (Y (i, a)) * MvPolynomial.X (a, b) := by sorry
