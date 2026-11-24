-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_coordMap_intertwines
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.coordMap_intertwines
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:59.556263+00:00
-- url     : https://prove2.me/theorems/c9118b1f-7c2d-43db-8de8-676b5e44cf17
-- title:
--   Local Lattice Bases: coord Map intertwines
-- statement:
--   The Local Lattice Bases construction uses the coord Map intertwines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/CoordMapInjective.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/CoordMapInjective.lean#L29-L34

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_CoordMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open Classical
variable {G : Type} [CommGroup G] [Fintype G] {Cl : Type} [Fintype Cl] [MulAction G Cl] {d : ℕ}
  {M : Type} [AddCommGroup M] [Module ℂ M]

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.coordMap_intertwines (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M)) (g : G) (φ : M)
    (x : G × (MulAction.orbitRel.Quotient G Cl × Fin d)) :
    t2xE Φ ρ (ρ g φ) x = t2xE Φ ρ φ (g * x.1, x.2) := by sorry
