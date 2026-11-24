-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_bracket
-- name    : Formalism.FourierDecayAlt.Q.EabGlW.loc_bracket
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:41:28.866139+00:00
-- url     : https://prove2.me/theorems/fac16977-ed42-4776-b1bb-b78b28bd2565
-- title:
--   Eab Gl W: loc bracket
-- statement:
--   The Eab Gl W construction uses the loc bracket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ExpMulVecFix.lean#L117-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GeneralLinearLevel/ExpMulVecFix.lean#L117-L142

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_VectorComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.Q.EabGlW.loc_bracket {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : Flow G X) (hY : Flow G Y) (hXY : Flow G (X * Y - Y * X))
    {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)} (hL : LocExt G f F U)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ U) (hgG : g ∈ G) :
    RdV X (RdV Y f) g - RdV Y (RdV X f) g = RdV (X * Y - Y * X) f g := by sorry
