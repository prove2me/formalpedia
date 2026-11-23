-- Prove2me | Theorems.Thm_Formalism_G0_CyclicSpanLengthLemmas_lengthPart2
-- name    : Formalism.G0.CyclicSpanLengthLemmas.lengthPart2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:57.066395+00:00
-- url     : https://prove2.me/theorems/3d54f439-ca5b-468e-8592-bd5f98c1b4da
-- title:
--   Cyclic Span Length Lemmas: length Part2
-- statement:
--   The Cyclic Span Length Lemmas construction uses the length Part2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbitsRefined.lean#L198-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/ManyOrbitsRefined.lean#L198-L350

import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbitsRefined
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
open Formalism.G0.CyclicSpanLengthLemmas
open ManyOrbitsP

theorem Formalism.G0.CyclicSpanLengthLemmas.lengthPart2 {R X : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup X] [Module R X] (π : R) (hπ : Irreducible π) (M N : Submodule R X)
    [Module.Free R M] [Module.Finite R M] (d : ℕ) (hd : Module.finrank R M = d)
    (τ S V : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2)
    (h1 : ∀ β < V, ∃ C : Finset X, (↑C : Set X) ⊆ M ∧
      (C.card : ℝ) ≤ d * s ^ (β + 1) ∧
      ∀ x ∈ M, π ^ (τ + β * S) • x ∈ N ⊔ Submodule.span R (↑C : Set X))
    (h2 : AllButLE π M N 0 (V * S)) :
    ∃ ℓ : ℕ, Module.length R (M ⧸ Submodule.comap M.subtype
        (N ⊓ (Ideal.span {π ^ τ}) • M)) = ℓ ∧
      (ℓ : ℝ) ≤ d * ((τ : ℝ) + 2 * S * s) := by sorry
