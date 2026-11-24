-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_ff_count
-- name    : Formalism.UG.P.tjcosets_ff_count
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:36:56.577794+00:00
-- url     : https://prove2.me/theorems/0ef9f53b-614f-408b-b89b-cc41789c76d7
-- title:
--   P: tjcosets ff count
-- statement:
--   The P construction uses the tjcosets ff count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L239-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L239-L266

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

theorem Formalism.UG.P.tjcosets_ff_count [Fintype 𝔽] (n j : ℕ) (hj : j ≤ n) :
    (tjcosets_par (𝔽 := 𝔽) n j).index *
        ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ (n - j) - Fintype.card 𝔽 ^ (i : ℕ)) =
      ∏ i : Fin (n - j), (Fintype.card 𝔽 ^ n - Fintype.card 𝔽 ^ (i : ℕ)) := by sorry
