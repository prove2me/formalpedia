-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_JA_SSn_Rep_Core_TC_PR_TW_core
-- name    : Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.core
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:34:39.70971+00:00
-- url     : https://prove2.me/theorems/22d5982c-ad6f-499b-a497-912c1ef3b648
-- title:
--   TW: core
-- statement:
--   The TW construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAPRTWNeAlg.lean#L348-L432
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJAPRTWNeAlg.lean#L348-L432

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlgSt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_StrictBoxOrder_core

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

theorem Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.core (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (E' : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V')
    (l l' : Fin (n + 1) → ℂ) (hE : GlRel E) (hIrr : Irr E) (hcap : ∀ (w : ℂ) (v : V), qdet E w v = cpol l w • v)
    (hE' : GlRel E') (hcap' : ∀ (w : ℂ) (v : V'), qdet E' w v = cpol l' w • v) (m p : Fin n → ℂ) (i : Fin n)
    (hm : SDec m) (hp : SDec p) (hpm : m = Function.update p i (p i - 1)) (hl : ∀ j, p i - 1 ≠ l j)
    (hl' : ∀ j, p i - 1 ≠ l' j) (hne : CapSp (subA E) p ≠ ⊥) (hne' : CapSp (subA E') p ≠ ⊥) (J : V' →ₗ[ℂ] V)
    (hJ : ∀ a b v, J (subA E' a b v) = subA E a b (J v)) (hJr : ∀ v, J v ∈ CapSp (subA E) m)
    (hinj : ∀ x ∈ CapSp (subA E') m, x ≠ 0 → J x ≠ 0) :
    ∃ v' : V', (∑ c, etaK E c (J (yK E' c v'))) ≠ 0 ∧ (∑ c, etaK E c (J (yK E' c v'))) ∈ CapSp (subA E) p := by sorry
