-- Prove2me | Theorems.Thm_AAInvW_ana_EcH_ext
-- name    : AAInvW.ana_EcH_ext
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:30:35.419929+00:00
-- url     : https://prove2.me/theorems/6171ccc0-0778-4541-b4ad-e5cf55cbcd7b
-- title:
--   AAInv W: ana Ec H ext
-- statement:
--   The AAInv W construction uses the ana Ec H ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L169-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/ConjugatedGeneratorGlRelation.lean#L169-L175

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SmoothLinear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_ConjugatedGeneratorGlRelation
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

theorem AAInvW.ana_EcH_ext (hH : HInvol H) {f F : Matrix (Fin n) (Fin n) ℂ → E} {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    {g : Matrix (Fin n) (Fin n) ℂ} (hU : IsOpen U) (hgU : g ∈ U) (hg : inUH H g) (hF : ContDiffOn ℝ ∞ F U)
    (hfF : ∀ h ∈ U, inUH H h → f h = F h) (Z : Matrix (Fin n) (Fin n) ℂ) :
    EcH H Z f g = fderiv ℝ F g (g * hpart1 H Z) + Complex.I • fderiv ℝ F g (g * hpart2 H Z) := by sorry
