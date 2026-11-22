-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_Fib_mk_eq_iff
-- name    : Formalism.L2.G.Cmp.Fib.mk_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:50.525592+00:00
-- url     : https://prove2.me/theorems/f2eb1e9d-0fac-4900-9541-388f73b8566a
-- title:
--   Fib: mk eq iff
-- statement:
--   The Fib construction uses the mk eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean#L20-L23

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsFib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.UG
open Formalism.L2.G.Cmp.Fib
variable {G Gp : Type} [Group G] [Group Gp] {K K' : Subgroup G} {Kp : Subgroup Gp} (X : Fib K K' Kp) (H : Subgroup G)

theorem Formalism.L2.G.Cmp.Fib.mk_eq_iff (S : Subgroup G) (a b : G) :
    (mkC H S a = mkC H S b) ↔ ∃ h ∈ H, ∃ κ ∈ S, b = h * a * κ := by sorry
