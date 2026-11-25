-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_of_dense_a
-- name    : Formalism.L2.S.Pv.SchurTens.SP_of_dense_a
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:24:55.312798+00:00
-- url     : https://prove2.me/theorems/3c851ffd-01e0-4ea9-a38e-c30ed897dfaa
-- title:
--   Schur Tens: SP of dense a
-- statement:
--   The Schur Tens construction uses the SP of dense a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensDense.lean#L100-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensDense.lean#L100-L140

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_EnergyAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_LimitMemLpAndIntegralEq
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensSpan
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_SchurTensDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.SchurTens
open Formalism.L2.SG.Pf.EnergyAbs
variable {K : Type} [TopologicalSpace K] [MeasurableSpace K] [OpensMeasurableSpace K]
  {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
  {m : Measure K} {σs : K → (Hs →L[ℂ] Hs)} {D : ℝ}

theorem Formalism.L2.S.Pv.SchurTens.SP_of_dense_a (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (b a' b' : Hs) (hA : ∀ a₀ ∈ Sp, SP m σs D a₀ b a' b')
    (hdiag : ∀ c ∈ Sp, SP m σs D c b c b) (hg : MemLp (coeff σs a' b') 2 m) (a : Hs) :
    SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by sorry
