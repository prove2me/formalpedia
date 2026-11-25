-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_integrable_termZ
-- name    : Formalism.FourierDecayAlt.P.PBK.integrable_termZ
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:01:41.801292+00:00
-- url     : https://prove2.me/theorems/f3833c33-6740-5a07-a34e-75b8f5b66375
-- title:
--   PBK: integrable term Z
-- statement:
--   The PBK construction uses the integrable term Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoSmulCocompact.lean#L38-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TendstoSmulCocompact.lean#L38-L45

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermRealisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LastBlockDecay
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormOfMemRootSetOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoIntegralPsiMoving
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBK
open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace
noncomputable section
open Classical
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem Formalism.FourierDecayAlt.P.PBK.integrable_termZ {s : ℕ} (_hs : s ≠ 0) (β : ℂ) {bt bt' : ℂ → H} (hb : MemLp (bz s bt) 2 volume)
    (hb' : MemLp (bz s bt') 2 volume) (x x' ρ ζ : ℂ) (hρ : ρ ≠ 0) (hζ : ζ ≠ 0) :
    Integrable (termZ s β bt bt' x x' ρ ζ) := by sorry
