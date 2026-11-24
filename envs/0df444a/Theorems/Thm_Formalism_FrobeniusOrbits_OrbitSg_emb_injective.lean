-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_OrbitSg_emb_injective
-- name    : Formalism.FrobeniusOrbits.OrbitSg.emb_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:27:13.654378+00:00
-- url     : https://prove2.me/theorems/a89305cd-0e77-4401-8c11-497f8b1912a1
-- title:
--   Orbit Sg: emb injective
-- statement:
--   The Orbit Sg construction uses the emb injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrbitSg.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/OrbitSg.lean#L25-L35

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

theorem Formalism.FrobeniusOrbits.OrbitSg.emb_injective {e : ℕ} (τ : GG e) : Function.Injective (emb τ) := by sorry
