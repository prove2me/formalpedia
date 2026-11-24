-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_li_map
-- name    : Formalism.HN.PlaceDecomposition.li_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:39.884093+00:00
-- url     : https://prove2.me/theorems/e92583ba-9496-40a7-a51f-b98737eb1e70
-- title:
--   Place Decomposition: li map
-- statement:
--   The Place Decomposition construction uses the li map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L61-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L61-L117

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition

theorem Formalism.HN.PlaceDecomposition.li_map {K L : Type*} [Field K] [Field L] (σ : K →+* L) {n m : Type*} [Fintype n]
    [Fintype m] [DecidableEq n] [DecidableEq m] (u : n → m → K) (hu : LinearIndependent K u) :
    LinearIndependent L (fun k i => σ (u k i)) := by sorry
