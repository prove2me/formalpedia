-- Prove2me | Theorems.Thm_Formalism_HN_ex_bounds
-- name    : Formalism.HN.ex_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:59.34186+00:00
-- url     : https://prove2.me/theorems/aa84f663-898b-4fdb-aa5e-af4d4aa1e11f
-- title:
--   HN: ex bounds
-- statement:
--   The HN construction uses the ex bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L143-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/Example.lean#L143-L174

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
open PolygonExample
local notation "ρx" => AddMonoidHom.id E2

theorem Formalism.HN.ex_bounds (N : Submodule ℤ E2) (hN : N ≤ Lx) :
    Formalism.F.rk N ≤ 2 ∧ Formalism.F.deg N ≤ 0 ∧ (Formalism.F.rk N = 2 → Formalism.F.deg N ≤ - Real.log 2) := by sorry
