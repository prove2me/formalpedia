-- Prove2me | Theorems.Thm_Formalism_ELL_PadicMultiplication_coeff_subst_smul
-- name    : Formalism.ELL.PadicMultiplication.coeff_subst_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:28.814796+00:00
-- url     : https://prove2.me/theorems/3f552825-5fe1-416b-b8fc-0d7ea7fbd8d9
-- title:
--   Padic Multiplication: coeff subst smul
-- statement:
--   The Padic Multiplication construction uses the coeff subst smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean#L109-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/PadicMult.lean#L109-L126

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

theorem Formalism.ELL.PadicMultiplication.coeff_subst_smul (l e : PowerSeries K) (hl0 : constantCoeff l = 0) (c : K) (n : ℕ) :
    coeff n (e.subst (c • l)) = (coeffPoly l e n).eval c := by sorry
