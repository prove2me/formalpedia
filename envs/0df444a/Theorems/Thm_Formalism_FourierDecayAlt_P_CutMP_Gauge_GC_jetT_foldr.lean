-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_jetT_foldr
-- name    : Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_foldr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:52.312098+00:00
-- url     : https://prove2.me/theorems/3697f113-7da3-4d16-8de2-38afb2465073
-- title:
--   GC: jet T foldr
-- statement:
--   The GC construction uses the jet T foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTJet.lean#L136-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutGCoreGTCLRadTJet.lean#L136-L150

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreGTCLRadTJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.jetT_foldr {g₀ : Q.Mx k r} (L : List ((Q.Mx k r → E) → (Q.Mx k r → E)))
    (hL : ∀ T ∈ L, ∀ (N : ℕ) (h : Q.Mx k r → E), ZJ k r (N + 1) h g₀ → ZJ k r N (T h) g₀) :
    ∀ (N : ℕ) (f : Q.Mx k r → E), ZJ k r (N + L.length) f g₀ →
      ZJ k r N (L.foldr (fun T h => T h) f) g₀ := by sorry
