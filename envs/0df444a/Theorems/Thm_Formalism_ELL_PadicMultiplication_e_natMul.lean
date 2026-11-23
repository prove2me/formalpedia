-- Prove2me | Theorems.Thm_Formalism_ELL_PadicMultiplication_e_natMul
-- name    : Formalism.ELL.PadicMultiplication.e_natMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:41.811008+00:00
-- url     : https://prove2.me/theorems/5934dd5c-2843-47d1-a139-d37d384c75ea
-- title:
--   Padic Multiplication: e nat Mul
-- statement:
--   The Padic Multiplication construction uses the e nat Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean#L89-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean#L89-L98

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

theorem Formalism.ELL.PadicMultiplication.e_natMul (F : FormalGroup (unitBall K)) (l e : PowerSeries K)
    (hl : IsLog (F.map (unitBall K).subtype) l) (hel : e.subst l = X) (m : ℕ) :
    e.subst ((m : K) • l) = (mulN F m).map (unitBall K).subtype := by sorry
