-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_Fib_cls_iff
-- name    : Formalism.L2.G.Cmp.Fib.cls_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:10:47.468107+00:00
-- url     : https://prove2.me/theorems/fdc06311-2172-4aa7-bf98-ed0b9af4fd30
-- title:
--   Fib: cls iff
-- statement:
--   The Fib construction uses the cls iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean#L35-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean#L35-L68

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
include hy hp

theorem Formalism.L2.G.Cmp.Fib.cls_iff (i i' : ClassSet H K') (g g' : Gp) :
    mkC H K (y i * X.j g) = mkC H K (y i' * X.j g') ↔
      i = i' ∧ ∃ γ ∈ H, (y i)⁻¹ * γ * y i ∈ K' ∧ g'⁻¹ * (X.pr γ * g) ∈ Kp := by sorry
