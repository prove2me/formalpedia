-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBK_mainD_ae_eq
-- name    : Formalism.FourierDecayAlt.P.PBK.mainD_ae_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:22:35.781349+00:00
-- url     : https://prove2.me/theorems/90293cb5-a57a-409d-9907-be32af0567d2
-- title:
--   PBK: main D ae eq
-- statement:
--   The PBK construction uses the main D ae eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AestronglyMeasurableMainD.lean#L29-L36

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TendstoSmulCocompact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AestronglyMeasurableMainD
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

theorem Formalism.FourierDecayAlt.P.PBK.mainD_ae_eq {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ε ≠ 0) (bt : ℂ → H) (x : ℂ) :
    mainD s β ε bt x =ᵐ[volume] fun D => ∑ k ∈ Finset.range s,
      G.psi β ((s : ℂ) * NthRootMeasurability.R s k (ε * D) * x) • bt (NthRootMeasurability.R s k (ε * D)) := by sorry
