-- Prove2me | Theorems.Thm_Formalism_ELL_jetsTwo_of
-- name    : Formalism.ELL.jetsTwo_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:27:24.150661+00:00
-- url     : https://prove2.me/theorems/383a7088-cf95-4529-a235-bb019f1f9a20
-- title:
--   ELL: jets Two of
-- statement:
--   The ELL construction uses the jets Two of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L207-L274
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L207-L274

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
open Formalism Formalism.ELL
open Formalism.G Formalism.ELL.FormalGroupQuadraticJets Formalism.G.LogCR

theorem Formalism.ELL.jetsTwo_of (hN : Formalism.ELL.NPderiv.{u}) : Formalism.ELL.JetsTwo.{u} := by sorry
