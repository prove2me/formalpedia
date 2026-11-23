-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_cc_domega
-- name    : Formalism.ELL.FormalGroupQuadraticJets.cc_domega
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:40.908223+00:00
-- url     : https://prove2.me/theorems/af92aad7-f341-4cdd-990b-a7c1e07f3faf
-- title:
--   Formal Group Quadratic Jets: cc domega
-- statement:
--   The Formal Group Quadratic Jets construction uses the cc domega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L160-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L160-L177

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupQuadraticJets
open Formalism.G.LogCR
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem Formalism.ELL.FormalGroupQuadraticJets.cc_domega (F : FormalGroup (Formalism.G.unitBall K)) :
    PowerSeries.constantCoeff (PowerSeries.derivative K (omegaF F)) =
      ccd 0 (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries) := by sorry
