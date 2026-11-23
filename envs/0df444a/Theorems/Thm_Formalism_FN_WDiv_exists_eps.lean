-- Prove2me | Theorems.Thm_Formalism_FN_WDiv_exists_eps
-- name    : Formalism.FN.WDiv.exists_eps
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:20:57.050467+00:00
-- url     : https://prove2.me/theorems/3d7a0a36-bcd9-4063-8db3-97921182e49e
-- title:
--   WDiv: exists eps
-- statement:
--   The WDiv construction uses the exists eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPWDivision.lean#L76-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SuccessiveMinima/SuccessiveMinimaProofs/NPWDivision.lean#L76-L101

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
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
omit [CompleteSpace K]

theorem Formalism.FN.WDiv.exists_eps (g : ℕ → K) (r : ℝ) (hr : 0 < r) (hg : ConvOn g r) (hne : g ≠ 0) :
    ∃ ε : ℝ, 0 ≤ ε ∧ ε < 1 ∧ ∀ k, wdeg g r < k → ‖g k‖ * r ^ k ≤ ε * gNorm g r := by sorry
