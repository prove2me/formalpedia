-- Prove2me | Theorems.Thm_Formalism_FN_WDiv_series_bound
-- name    : Formalism.FN.WDiv.series_bound
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:24:53.194209+00:00
-- url     : https://prove2.me/theorems/b34c5f60-b8fc-4a04-85ba-62ac0a95c37b
-- title:
--   WDiv: series bound
-- statement:
--   The WDiv construction uses the series bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPWDivision.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPWDivision.lean#L19-L23

import Definitions.Def_Formalism_SuccessiveMinima_DefsNP
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NewtonSlope
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_NPWDivision
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Polynomial
noncomputable section
open Formalism Formalism.FN Formalism.FN.WDiv
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem Formalism.FN.WDiv.series_bound (u : ℕ → ℕ → K) {r : ℝ} (hr : 0 < r) (j : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖u i j‖ * r ^ j ≤ C) : ‖∑' i, u i j‖ * r ^ j ≤ C := by sorry
