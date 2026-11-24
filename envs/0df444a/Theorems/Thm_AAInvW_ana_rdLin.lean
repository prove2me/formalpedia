-- Prove2me | Theorems.Thm_AAInvW_ana_rdLin
-- name    : AAInvW.ana_rdLin
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:51:27.590889+00:00
-- url     : https://prove2.me/theorems/688f5803-c1b4-4657-b24d-3e8398add385
-- title:
--   AAInv W: ana rd Lin
-- statement:
--   The AAInv W construction uses the ana rd Lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L88-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SmoothLinear.lean#L88-L115

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_AnaHpartUnique
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
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
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem AAInvW.ana_rdLin (hH : HInvol H) {f f' : Matrix (Fin n) (Fin n) ℂ → E} (c : ℂ)
    {X g : Matrix (Fin n) (Fin n) ℂ} (hf : SmoothOnH H f) (hf' : SmoothOnH H f') (hX : inLH H X)
    (hg : inUH H g) : RdV X (fun x => f x + c • f' x) g = RdV X f g + c • RdV X f' g := by sorry
