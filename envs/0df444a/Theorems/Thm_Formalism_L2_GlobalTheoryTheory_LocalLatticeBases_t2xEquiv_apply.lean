-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_t2xEquiv_apply
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.t2xEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:08.188708+00:00
-- url     : https://prove2.me/theorems/ac5101c3-49f7-4f22-bc7d-21eb84375984
-- title:
--   Local Lattice Bases: t2x Equiv apply
-- statement:
--   The Local Lattice Bases construction uses the t2x Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/CoordMapInjective.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/CoordMapInjective.lean#L96-L99

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

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.t2xEquiv_apply (Φ : M ≃ₗ[ℂ] (Cl → Fin d → ℂ)) (ρ : G →* (M →ₗ[ℂ] M))
    (hmono : ∀ (g : G) (c : Cl) (φ : M), Φ (ρ g φ) c = 0 → Φ φ (g • c) = 0)
    (hfree : ∀ (g : G) (c : Cl), g • c = c → g = 1) (φ : M) :
    orbitDecompositionLinearEquiv Φ ρ hmono hfree φ = t2xE Φ ρ φ := by sorry
