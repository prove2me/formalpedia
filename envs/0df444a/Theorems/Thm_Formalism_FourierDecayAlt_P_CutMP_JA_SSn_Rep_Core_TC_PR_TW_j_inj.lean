-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_Rep_Core_TC_PR_TW_j_inj
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.j_inj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:33.66323+00:00
-- url     : https://prove2.me/theorems/3625a0b8-df25-48c0-a611-15a06e73b97c
-- title:
--   TW: j inj
-- statement:
--   The TW construction uses the j inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAPRTWNeAlg.lean#L212-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAPRTWNeAlg.lean#L212-L248

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
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
  [FiniteDimensional ℂ V']

theorem Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.j_inj (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (E' : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V')
    (β' : ℂ) (L' : Fin (n + 1) → ℤ) (M' : Fin n → ℤ) (hE' : Hyp E' β' L') (hM' : Box L' M')
    (J : V' →ₗ[ℂ] V) (hJ0 : J ≠ 0) (hJ : ∀ a b v, J (subA E' a b v) = subA E a b (J v))
    (hJr : ∀ v, J v ∈ CapSp (subA E) (shf β' M')) (x : V') (hx : x ∈ CapSp (subA E') (shf β' M')) (hx0 : x ≠ 0) :
    J x ≠ 0 := by sorry
