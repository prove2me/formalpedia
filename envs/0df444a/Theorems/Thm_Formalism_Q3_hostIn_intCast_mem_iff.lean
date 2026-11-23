-- Prove2me | Theorems.Thm_Formalism_Q3_hostIn_intCast_mem_iff
-- name    : Formalism.Q3.hostIn_intCast_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:46.458225+00:00
-- url     : https://prove2.me/theorems/fb08bd51-b2d3-46c7-98fd-32bf7325ee0c
-- title:
--   Q3: host In int Cast mem iff
-- statement:
--   The Q3 construction uses the host In int Cast mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostInertia.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CMTypeGalois/CMTypeFrobenius/HostInertia.lean#L10-L14

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostInertia
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.Q3

theorem Formalism.Q3.hostIn_intCast_mem_iff {E : Type} [Field E] [NumberField E] (p : ℕ)
    (P : Ideal (𝓞 E)) [P.LiesOver (span {(p : ℤ)})] (n : ℤ) :
    (n : 𝓞 E) ∈ P ↔ (p : ℤ) ∣ n := by sorry
