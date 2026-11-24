-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_Rep_Core_TC_PR_TW_fam_zero
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.fam_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:29.192107+00:00
-- url     : https://prove2.me/theorems/4fc096e2-99db-4d14-89d7-bda4c35816e9
-- title:
--   TW: fam zero
-- statement:
--   The TW construction uses the fam zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAPRTWNeAlg.lean#L153-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAPRTWNeAlg.lean#L153-L187

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

theorem Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.fam_zero [FiniteDimensional ℂ V] {n : ℕ} (F : Fin n → Fin n → Module.End ℂ V) (hF : GlRel F) (m : Fin n → ℂ)
    (hm : SDec m) (i : Fin n) (Φ : Fin n → V) (hmem : ∀ c, Φ c ∈ CapSp F m)
    (hd : ∀ a c, F a a (Φ c) = (m a + ((a : ℕ) : ℂ) + (if a = i then 1 else 0) - if a = c then 1 else 0) • Φ c)
    (hr : ∀ a b c, a < b → F a b (Φ c) = if a = c then -(Φ b) else 0) (h0 : Φ i = 0) : ∀ c, Φ c = 0 := by sorry
