-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_hatOK_of_poly
-- name    : Formalism.FourierDecayAlt.P.CutMP.hatOK_of_poly
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:04:08.562809+00:00
-- url     : https://prove2.me/theorems/e4cbc4cf-6ede-580e-9dc1-afdf3cb47e14
-- title:
--   Cut MP: hat OK of poly
-- statement:
--   The Cut MP construction uses the hat OK of poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHatOpA.lean#L67-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CutJDHatOpA.lean#L67-L86

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
open NumberField
noncomputable section

theorem Formalism.FourierDecayAlt.P.CutMP.hatOK_of_poly (hP : JDPolyOK) {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Wp Wq : InfinitePlace E → Type}
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    {Cc : ℝ} (hCc : 1 ≤ Cc) {S : C.HidaSetting E Wp Wq}
    {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))} {v : Fin S.f}
    {Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    (hΘ : PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ)
    (hc : B.Commutes (T v).base (B.GPos (T v).base) Θ) : HatOK Cc S T v Θ := by sorry
