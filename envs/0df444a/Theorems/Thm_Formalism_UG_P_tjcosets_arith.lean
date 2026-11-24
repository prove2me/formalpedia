-- Prove2me | Theorems.Thm_Formalism_UG_P_tjcosets_arith
-- name    : Formalism.UG.P.tjcosets_arith
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:17.623774+00:00
-- url     : https://prove2.me/theorems/16f7e2ca-b73e-4955-a6dc-c88ad16235a3
-- title:
--   P: tjcosets arith
-- statement:
--   The P construction uses the tjcosets arith property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean#L36-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Tjcosets.lean#L36-L66

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

theorem Formalism.UG.P.tjcosets_arith (q n j C : ℕ) (hq : 2 ≤ q) (hj : j ≤ n)
    (h : C * ∏ i : Fin (n - j), (q ^ (n - j) - q ^ (i : ℕ)) =
      ∏ i : Fin (n - j), (q ^ n - q ^ (i : ℕ))) :
    (C : ℤ) * ∏ i ∈ Finset.range j, ((q : ℤ) ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range j, ((q : ℤ) ^ (n - i) - 1) := by sorry
