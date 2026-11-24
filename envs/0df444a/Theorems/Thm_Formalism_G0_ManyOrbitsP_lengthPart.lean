-- Prove2me | Theorems.Thm_Formalism_G0_ManyOrbitsP_lengthPart
-- name    : Formalism.G0.ManyOrbitsP.lengthPart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:19.026283+00:00
-- url     : https://prove2.me/theorems/050ec3a9-2e9c-4001-babd-20517efbfd13
-- title:
--   Many Orbits P: length Part
-- statement:
--   The Many Orbits P construction uses the length Part property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L135-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbits.lean#L135-L192

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.G0
open Formalism.G0.ManyOrbitsP

theorem Formalism.G0.ManyOrbitsP.lengthPart {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X] (π : R) (hπ : Irreducible π) (M N : Submodule R X)
    [Module.Free R M] [Module.Finite R M] (d : ℕ) (hd : Module.finrank R M = d)
    (τ S V β₀ : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (h1 : ∀ β ≤ β₀, ∃ C : Finset X, (↑C : Set X) ⊆ M ∧
      (C.card : ℝ) ≤ 2 * d * (s ^ (β + 1) / (β + 1).factorial) ∧
      ∀ x ∈ M, π ^ (τ + β * S) • x ∈ N ⊔ Submodule.span R (↑C : Set X))
    (h2 : AllButLE π M N 0 (V * S)) :
    ∃ ℓ : ℕ, Module.length R (M ⧸ Submodule.comap M.subtype
        (N ⊓ (Ideal.span {π ^ τ}) • M)) = ℓ ∧
      (ℓ : ℝ) ≤ d * (τ + 4 * S * s + V * S * (2 * s ^ (β₀ + 1) / (β₀ + 1).factorial)) := by sorry
