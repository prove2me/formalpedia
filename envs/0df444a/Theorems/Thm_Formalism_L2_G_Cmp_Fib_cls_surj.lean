-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_Fib_cls_surj
-- name    : Formalism.L2.G.Cmp.Fib.cls_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:56.80452+00:00
-- url     : https://prove2.me/theorems/53f2b26c-ff2c-4d9b-a789-c53a6badcbbf
-- title:
--   Fib: cls surj
-- statement:
--   The Fib construction uses the cls surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean#L72-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean#L72-L77

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
variable (y : ClassSet H K' → G) (hy : ∀ i, mkC H K' (y i) = i) (hp : ∀ i, X.pr (y i) = 1)
include hy

theorem Formalism.L2.G.Cmp.Fib.cls_surj (x : G) : ∃ i g, mkC H K (y i * X.j g) = mkC H K x := by sorry
