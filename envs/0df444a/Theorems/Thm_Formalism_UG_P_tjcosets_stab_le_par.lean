-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_stab_le_par
-- name    : Formalism.UG.P.tjcosets_stab_le_par
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:37:57.231141+00:00
-- url     : https://prove2.me/theorems/743b53bd-9954-4b9d-864d-ca57581b1121
-- title:
--   P: tjcosets stab le par
-- statement:
--   The P construction uses the tjcosets stab le par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L148-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/TjcosetsFF.lean#L148-L161

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

theorem Formalism.UG.P.tjcosets_stab_le_par [Finite 𝔽] (n j : ℕ) :
    MulAction.stabilizer (GL (Fin n) 𝔽) (standardBasisTuple n j : TjcosetsFr (n - j) n 𝔽) ≤
      tjcosets_par n j := by sorry
