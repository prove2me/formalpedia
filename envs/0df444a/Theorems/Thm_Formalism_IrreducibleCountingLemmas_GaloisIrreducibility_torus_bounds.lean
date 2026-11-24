-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_torus_bounds
-- name    : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.torus_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:06.135671+00:00
-- url     : https://prove2.me/theorems/86502fab-292a-4e6d-b164-4ca6adc6df77
-- title:
--   Galois Irreducibility: torus bounds
-- statement:
--   The Galois Irreducibility construction uses the torus bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaLWeight.lean#L5-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/IRRLemmaLWeight.lean#L5-L38

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.torus_bounds (g : ℕ) (hg : 2 ≤ g) (d : Multiset ℕ) : (∀ x ∈ d, 1 ≤ x) →
    0 < (d.map (fun x => (g : ℝ) ^ x - 1)).prod ∧
    (d.map (fun x => (g : ℝ) ^ x - 1)).prod ≤ (g : ℝ) ^ d.sum ∧
    (g : ℝ) ^ d.sum * (1 - (d.card : ℝ) / g) ≤ (d.map (fun x => (g : ℝ) ^ x - 1)).prod := by sorry
