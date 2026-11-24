-- Prove2me | Theorems.Thm_Formalism_L2_SG_ClassAct_mem_FixAt
-- name    : Formalism.L2.SG.ClassAct.mem_FixAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:32.743796+00:00
-- url     : https://prove2.me/theorems/36e1b2f1-e20f-4dca-b354-627f3323680c
-- title:
--   Class Act: mem Fix At
-- statement:
--   The Class Act construction uses the mem Fix At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ClassAct.lean#L77-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/ClassAct.lean#L77-L87

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.ClassAct
open Formalism.UG Module
variable {G : Type} [Group G]

theorem Formalism.L2.SG.ClassAct.mem_FixAt {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W] {Γ K : Subgroup G}
    {ρ : Representation k Γ W} {χ : K →* kˣ} {D : Subgroup G} {f : G → W} :
    f ∈ FixAt k Γ K ρ χ D ↔ f ∈ AMFChi k Γ K ρ χ ∧ ∀ δ ∈ D, ∀ g : G, f (g * δ) = f g := by sorry
