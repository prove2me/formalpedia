-- Prove2me | Theorems.Thm_DirectedHamiltonicity_Main_prepare_cycle_parity_query_poly
-- name    : DirectedHamiltonicity.Main.prepare_cycle_parity_query_poly
-- status  : Proved
-- author  : @Soh Kumabe
-- created : 2026-11-27T02:21:58.637142+00:00
-- url     : https://prove2.me/theorems/9a021894-96f2-4d50-ad7e-aafd5012472c
-- title:
--   A polynomial-time encoder for the weighted parity queries in directed cycle search
-- statement:
--   One fixed binary program takes an explicit Boolean matrix and an arbitrary natural-number trial rank. It returns the exact self-delimiting weighted-path instance specified by the cycle search, or an empty list when the trial does not issue a parity call. Its running time is polynomial in the binary input length.
-- source:
--   T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, Section 2, proof of Theorem 1. https://arxiv.org/html/2609.39062v2#S2

import Definitions.Def_DirectedHamiltonicity_CycleSearch
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime

open DirectedHamiltonicity.Main DirectedHamiltonicity.Main.CycleReduction

theorem DirectedHamiltonicity.Main.prepare_cycle_parity_query_poly :
    ∃ prepare : List (List Bool) × ℕ → List Bool, OAI.MetricKMedian.Binary.Automatic.Poly prepare ∧
      ∀ (n : ℕ) (adj : Fin n → Fin n → Bool) (word : ℕ),
        prepare (List.ofFn (fun u => List.ofFn (adj u)),word) =
          if h : word < drawCount n then (candidateInput adj ((rankDraw n).symm ⟨word,h⟩)).getD [] else [] := by sorry
