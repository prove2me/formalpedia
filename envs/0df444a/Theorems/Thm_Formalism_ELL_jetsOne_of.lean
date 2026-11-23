-- Prove2me | Theorems.Thm_Formalism_ELL_jetsOne_of
-- name    : Formalism.ELL.jetsOne_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:36.713251+00:00
-- url     : https://prove2.me/theorems/053d9052-c1d9-44e5-a78f-7c1f0cc59b54
-- title:
--   ELL: jets One of
-- statement:
--   The ELL construction uses the jets One of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsOne.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsOne.lean#L38-L51

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.G Formalism.ELL.FormalGroupLinearJets

theorem Formalism.ELL.jetsOne_of (hN : Formalism.ELL.NPderiv.{u}) : Formalism.ELL.JetsOne.{u} := by sorry
