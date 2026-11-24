-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_Rep_Core_TC_PR_TW_z_main
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.z_main
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:33:48.865071+00:00
-- url     : https://prove2.me/theorems/62d8366e-58a2-40d7-8264-2664f53bf8e2
-- title:
--   TW: z main
-- statement:
--   The TW construction uses the z main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAPRTWNeAlg.lean#L57-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAPRTWNeAlg.lean#L57-L128

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlgSt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.z_main (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (l : Fin (n + 1) → ℂ) (hE : GlRel E)
    (hcap : ∀ (w : ℂ) (v : V), qdet E w v = cpol l w • v) (p : Fin n → ℂ) (hp : Function.Injective p) (i : Fin n)
    (hl : ∀ j, p i - 1 ≠ l j) (v : V) (hv : v ∈ CapSp (subA E) p) :
    (∀ x, qdet (subA E) (-p i) (yK E x v) ∈ CapSp (subA E) (Function.update p i (p i - 1))) ∧
      ∃ t : ℂ, t ≠ 0 ∧ ∑ x, etaK E x (qdet (subA E) (-p i) (yK E x v)) = t • v := by sorry
