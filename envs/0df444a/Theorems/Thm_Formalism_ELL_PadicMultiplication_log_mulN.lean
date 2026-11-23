-- Prove2me | Theorems.Thm_Formalism_ELL_PadicMultiplication_log_mulN
-- name    : Formalism.ELL.PadicMultiplication.log_mulN
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:32.471161+00:00
-- url     : https://prove2.me/theorems/ab91a90f-1a71-42e1-b293-66d364eba25f
-- title:
--   Padic Multiplication: log mul N
-- statement:
--   The Padic Multiplication construction uses the log mul N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean#L61-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean#L61-L79

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.ELL Formalism.ELL.PadicMultiplication
open Formalism.G Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.PadicMultiplication.log_mulN (F : FormalGroup (unitBall K)) (l : PowerSeries K)
    (hl : IsLog (F.map (unitBall K).subtype) l) (m : ℕ) :
    l.subst ((mulN F m).map (unitBall K).subtype) = (m : K) • l := by sorry
