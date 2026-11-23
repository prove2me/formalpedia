-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_cc_omega
-- name    : Formalism.ELL.FormalGroupQuadraticJets.cc_omega
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:00.721197+00:00
-- url     : https://prove2.me/theorems/0fadb2e0-1826-4894-8cd4-791c714e4e04
-- title:
--   Formal Group Quadratic Jets: cc omega
-- statement:
--   The Formal Group Quadratic Jets construction uses the cc omega property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L151-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L151-L154

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

theorem Formalism.ELL.FormalGroupQuadraticJets.cc_omega (F : FormalGroup (Formalism.G.unitBall K)) :
    PowerSeries.constantCoeff (omegaF F) = ccd 1 (FK F).toPowerSeries := by sorry
