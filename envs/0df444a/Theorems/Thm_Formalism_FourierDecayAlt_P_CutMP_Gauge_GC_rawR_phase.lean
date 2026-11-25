-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_rawR_phase
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.rawR_phase
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:22:54.169867+00:00
-- url     : https://prove2.me/theorems/6dc32c71-8007-468a-826c-fed6db016b4b
-- title:
--   GC: raw R phase
-- statement:
--   The GC construction uses the raw R phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTConnGaugeA.lean#L102-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTConnGaugeA.lean#L102-L108

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_cut_GCore_GTConnCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTConnGaugeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.rawR_phase (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (u : M.Ty P → ℂ → ℂ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) :
    rawR P μsec (fun ρ ζ => u ρ ζ • e ρ ζ) Φ ρ = fun q => star (u ρ q.1.2) * rawR P μsec e Φ ρ q := by sorry
