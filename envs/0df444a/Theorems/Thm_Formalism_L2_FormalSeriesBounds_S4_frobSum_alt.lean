-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_S4_frobSum_alt
-- name    : Formalism.L2.FormalSeriesBounds.S4.frobSum_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:04.109221+00:00
-- url     : https://prove2.me/theorems/d1d86f85-0e91-4e17-bb4b-5f3e7f5a348f
-- title:
--   S4: frob Sum alt
-- statement:
--   The S4 construction uses the frob Sum alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L202-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ExistsStrictMonoMinor.lean#L202-L248

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ExistsStrictMonoMinor
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.S4

theorem Formalism.L2.FormalSeriesBounds.S4.frobSum_alt {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (big : ZMod d → Prop)
    (halt : ∀ b, big (b + 1) ↔ ¬ big b) (p : ZMod d → ℕ)
    (hpb : ∀ b, big b → p b = n + j) (hps : ∀ b, ¬ big b → p b = j')
    (a : ZMod d) (ha : big a) :
    frobSum l p a = (j' : ℝ) * gam l + ((n : ℝ) + j) * rho l := by sorry
