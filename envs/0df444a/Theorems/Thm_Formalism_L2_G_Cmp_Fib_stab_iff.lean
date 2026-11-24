-- Prove2me | Theorems.Thm_Formalism_L2_G_Cmp_Fib_stab_iff
-- name    : Formalism.L2.G.Cmp.Fib.stab_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:37.624886+00:00
-- url     : https://prove2.me/theorems/b14f9c66-b50f-4ffa-bef8-8a17aab790fb
-- title:
--   Fib: stab iff
-- statement:
--   The Fib construction uses the stab iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean#L81-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/ComparisonMaps/ClsFib.lean#L81-L97

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
include hp

theorem Formalism.L2.G.Cmp.Fib.stab_iff (i : ClassSet H K') (g : Gp) (γ : G) :
    (y i * X.j g)⁻¹ * γ * (y i * X.j g) ∈ K ↔ (y i)⁻¹ * γ * y i ∈ K' ∧ g⁻¹ * (X.pr γ * g) ∈ Kp := by sorry
