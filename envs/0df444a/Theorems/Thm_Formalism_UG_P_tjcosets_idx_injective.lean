-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_idx_injective
-- name    : Formalism.UG.P.tjcosets_idx_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:51.517801+00:00
-- url     : https://prove2.me/theorems/0495caa3-42bb-42be-9fbc-c6ea135b2092
-- title:
--   P: tjcosets idx injective
-- statement:
--   The P construction uses the tjcosets idx injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L32-L36

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
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
variable {𝔽 : Type} [Field 𝔽]

theorem Formalism.UG.P.tjcosets_idx_injective (n j : ℕ) : Function.Injective (tjcosets_idx n j) := by sorry
