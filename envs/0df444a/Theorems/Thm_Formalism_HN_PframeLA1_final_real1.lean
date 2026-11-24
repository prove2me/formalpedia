-- Prove2me | Theorems.Thm_Formalism_HN_PframeLA1_final_real1
-- name    : Formalism.HN.PframeLA1.final_real1
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:24:13.78883+00:00
-- url     : https://prove2.me/theorems/3943946c-aa7d-4acc-9404-e010f3042f65
-- title:
--   Pframe LA1: final real1
-- statement:
--   The Pframe LA1 construction uses the final real1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/FrameLinearAlgebraFirst.lean#L15-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/FrameLinearAlgebraFirst.lean#L15-L64

import Mathlib
import Definitions.Def_Formalism_HarderNarasimhan_StatementFrameF
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FrameLinearAlgebraFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PframeLA1
open Finset Module LinearMap Formalism.CorankShareLayerCake.FR Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open scoped InnerProductSpace

theorem Formalism.HN.PframeLA1.final_real1 (D R w e ε η t X tW : ℝ) (hD : 0 < D) (hR : 0 < R) (he0 : 0 ≤ e) (he : e ≤ 1/4)
    (hε : 0 ≤ ε) (hw0 : 0 ≤ w) (hwD : w ≤ D) (ht : R * (1 - √e) ≤ t) (hX0 : 0 ≤ X)
    (hX : X ≤ η * t ^ 2 / D) (hlow : t / D * w - √w * √X ≤ tW)
    (hup : tW ≤ ε * R + R * √(ε * e)) : w ≤ (η + 4 * ε + 4 * √e) * D := by sorry
