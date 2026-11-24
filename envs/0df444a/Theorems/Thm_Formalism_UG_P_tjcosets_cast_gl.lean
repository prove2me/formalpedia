-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_cast_gl
-- name    : Formalism.UG.P.tjcosets_cast_gl
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:38.009121+00:00
-- url     : https://prove2.me/theorems/0f1d30f0-5392-4bb1-83ec-c3bef17687a5
-- title:
--   P: tjcosets cast gl
-- statement:
--   The P construction uses the tjcosets cast gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean#L25-L34

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

theorem Formalism.UG.P.tjcosets_cast_gl (q N m : ℕ) (hq : 1 ≤ q) (hm : m ≤ N) :
    ((∏ i : Fin m, (q ^ N - q ^ (i : ℕ)) : ℕ) : ℤ) =
      (q : ℤ) ^ (∑ i ∈ Finset.range m, i) * ∏ i ∈ Finset.range m, ((q : ℤ) ^ (N - i) - 1) := by sorry
