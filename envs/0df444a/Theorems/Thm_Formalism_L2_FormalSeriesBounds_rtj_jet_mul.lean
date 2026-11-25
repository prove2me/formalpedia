-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_jet_mul
-- name    : Formalism.L2.FormalSeriesBounds.rtj_jet_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:24:55.901096+00:00
-- url     : https://prove2.me/theorems/fb627860-5c6d-439f-99ad-fd222fd44738
-- title:
--   Formal Series Bounds: rtj jet mul
-- statement:
--   The Formal Series Bounds construction uses the rtj jet mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L77-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L77-L122

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}

theorem Formalism.L2.FormalSeriesBounds.rtj_jet_mul (A : Set σ) (P Q : MvPolynomial σ K) (F G : MvPowerSeries σ K)
    (hP : P ∈ MvPolynomial.supported K A) (hQ : Q ∈ MvPolynomial.supported K Aᶜ)
    (hF : rtjSerIn A F) (hG : rtjSerIn Aᶜ G) :
    jetAt0 (P * Q) (F * G) = jetAt0 P F * jetAt0 Q G := by sorry
