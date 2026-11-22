-- Prove2me | Theorems.Thm_Formalism_HN_PlaceDecomposition_psi_apply
-- name    : Formalism.HN.PlaceDecomposition.psi_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:57:37.842938+00:00
-- url     : https://prove2.me/theorems/680f7097-c813-4a92-8e32-fd388c68c61e
-- title:
--   Place Decomposition: psi apply
-- statement:
--   The Place Decomposition construction uses the psi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L135-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PlaceSplit.lean#L135-L136

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
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]

theorem Formalism.HN.PlaceDecomposition.psi_apply (v : P) (z : ι → ℂ) (p : P × ι × Fin 2) :
    psi v z p = if p.1 = v then (if p.2.2 = 0 then (z p.2.1).re else (z p.2.1).im) else 0 := by sorry
