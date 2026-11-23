-- Prove2me | Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_linearCoeff_one_formal_group_law
-- name    : Formalism.ELL.FormalGroupQuadraticJets.linearCoeff_one_formal_group_law
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:46.445833+00:00
-- url     : https://prove2.me/theorems/20b19c74-8c7f-4911-8dfb-6d53cfaf3e5c
-- title:
--   Formal Group Quadratic Jets: linear Coeff one formal group law
-- statement:
--   The Formal Group Quadratic Jets construction uses the linear Coeff one formal group law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L197-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/JetsTwo.lean#L197-L199

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

theorem Formalism.ELL.FormalGroupQuadraticJets.linearCoeff_one_formal_group_law (F : FormalGroup (Formalism.G.unitBall K)) : ccd 1 (FK F).toPowerSeries = 1 := by sorry
