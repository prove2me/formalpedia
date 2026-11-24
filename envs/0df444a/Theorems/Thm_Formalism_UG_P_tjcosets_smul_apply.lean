-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_smul_apply
-- name    : Formalism.UG.P.tjcosets_smul_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:37:49.216274+00:00
-- url     : https://prove2.me/theorems/315adbc3-4c08-408e-922f-b96100938a3f
-- title:
--   P: tjcosets smul apply
-- statement:
--   The P construction uses the tjcosets smul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L27-L28

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

theorem Formalism.UG.P.tjcosets_smul_apply {m n : ℕ} (g : GL (Fin n) 𝔽) (w : TjcosetsFr m n 𝔽) (i : Fin m) :
    (g • w) i = (g : Matrix (Fin n) (Fin n) 𝔽) *ᵥ w i := by sorry
