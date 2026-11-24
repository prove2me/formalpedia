-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_fst_sum
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.fst_sum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:57:59.930171+00:00
-- url     : https://prove2.me/theorems/02982fe2-16bd-4b09-9e09-ae543e2fffce
-- title:
--   Gauge: fst sum
-- statement:
--   The Gauge construction uses the fst sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGaugeCut.lean#L127-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGaugeCut.lean#L127-L128

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGaugeCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge
noncomputable section
variable (P : M.Par)

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.fst_sum {ι : Type} (s : Finset ι) (x : ι → (MA.DQ P).Pr) : (∑ i ∈ s, x i).1 = ∑ i ∈ s, (x i).1 := by sorry
