-- Prove2me | Theorems.Thm_Formalism_L2_SG_RowsOther_ngInputs_iff
-- name    : Formalism.L2.SG.RowsOther.ngInputs_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:51.7387+00:00
-- url     : https://prove2.me/theorems/bebb1aa5-fbcc-4e6f-8ea2-cc1bab4c9064
-- title:
--   Rows Other: ng Inputs iff
-- statement:
--   The Rows Other construction uses the ng Inputs iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L140-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RowsOther.lean#L140-L144

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementPN
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RowsOther
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.RowsOther
open Formalism.FourierDecayAlt
variable {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (X : PB.Terms τ Rw I H H₁)
variable {E : Type} [Field E] [NumberField E] {r : ℕ} {Cl Nu : Type} (N : PN.NGData τ E r Cl Nu)

theorem Formalism.L2.SG.RowsOther.ngInputs_iff (k f C1 C0 A : ℕ) (CB b rd g TT cSt AAre e1 Ire : ℝ) :
    PN.NGInputs X N k f C1 C0 A CB b rd g TT cSt AAre e1 Ire ↔
      NGFin X N k f C1 C0 rd g TT AAre e1 ∧ NGReal X N f A CB b cSt Ire := by sorry
