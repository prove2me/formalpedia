-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_OrbitSg_sg_fst_ne_one
-- name    : Formalism.FrobeniusOrbits.OrbitSg.sg_fst_ne_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:31:16.666827+00:00
-- url     : https://prove2.me/theorems/8dae2d2d-9f19-4421-87fc-b0675bb5385e
-- title:
--   Orbit Sg: sg fst ne one
-- statement:
--   The Orbit Sg construction uses the sg fst ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrbitSg.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrbitSg.lean#L22-L23

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Orbits
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_OrbitSg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.OrbitSg

theorem Formalism.FrobeniusOrbits.OrbitSg.sg_fst_ne_one (e : ℕ) : (sg e).1 ≠ 1 := by sorry
