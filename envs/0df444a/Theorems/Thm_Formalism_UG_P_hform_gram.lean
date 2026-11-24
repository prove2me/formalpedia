-- Prove2me | Theorems.Thm_Formalism_UG_P_hform_gram
-- name    : Formalism.UG.P.hform_gram
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:31:21.785129+00:00
-- url     : https://prove2.me/theorems/48fabb52-d263-4e56-8698-ccc54b9e52e8
-- title:
--   P: hform gram
-- statement:
--   The P construction uses the hform gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Bridge.lean#L48-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Bridge.lean#L48-L62

import Definitions.Def_Formalism_SatakeDualWeyl_StatementB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P

theorem Formalism.UG.P.hform_gram {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (x y : n → K) :
    h x y = Formalism.UG.hform (starRingEnd K) (Formalism.UG.gram h) x y := by sorry
