-- Prove2me | Theorems.Thm_Formalism_L2_S_Pv_SchurTens_SP_of_dense_b
-- name    : Formalism.L2.S.Pv.SchurTens.SP_of_dense_b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:25:27.477216+00:00
-- url     : https://prove2.me/theorems/1b62a650-9482-440e-8661-a3cda6f7e23d
-- title:
--   Schur Tens: SP of dense b
-- statement:
--   The Schur Tens construction uses the SP of dense b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensDense.lean#L142-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/TraceIntegralEstimates/SchurTensDense.lean#L142-L182

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

theorem Formalism.L2.S.Pv.SchurTens.SP_of_dense_b (hstr : ∀ a : Hs, Continuous (fun x => σs x a)) (hD : 0 < D) (Sp : Submodule ℂ Hs)
    (hdense : Dense (Sp : Set Hs)) (a a' b' : Hs) (hB : ∀ b₀ ∈ Sp, SP m σs D a b₀ a' b')
    (hdiag : ∀ c ∈ Sp, SP m σs D a c a c) (hg : MemLp (coeff σs a' b') 2 m) (b : Hs) :
    SP m σs D a b a' b' ∧ MemLp (coeff σs a b) 2 m := by sorry
