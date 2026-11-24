-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_tj_ne_zero
-- name    : Formalism.UG.P.tjcosets_tj_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T10:38:06.475851+00:00
-- url     : https://prove2.me/theorems/1a8d03c6-5689-4ea4-9649-244274b7e1c4
-- title:
--   P: tjcosets tj ne zero
-- statement:
--   The P construction uses the tjcosets tj ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean#L157-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean#L157-L169

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Matrix
open scoped WithZero
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG

theorem Formalism.UG.P.tjcosets_tj_ne_zero {L : Type} [Field L] (O : Subring L) (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0)
    (g : GL (Fin n) L) :
    Tj ℤ n O ϖ j g ≠ 0 ↔
      ∃ a ∈ GLint (Fin n) O, ∃ b ∈ GLint (Fin n) O, g = a * tjcosets_dG n j ϖ hϖ * b := by sorry
