-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_theorem_3_2
-- name    : DirectedGlobalMincut.Sampling.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:18.558248+00:00
-- url     : https://prove2.me/theorems/e0868941-fdb6-4e67-b1c0-a3e2037cba11
-- title:
--   Theorem 3.2 — Compute two edge-disjoint rooted arborescences
-- statement:
--   For any finite directed graph $H=(V,E)$ and root $s\in V$, one deterministic algorithm, without an optimization oracle, computes two edge-disjoint spanning out-arborescences rooted at $s$ whenever such a pair exists:
--
--   $$T_1\cap T_2=\varnothing.$$
--
--   Its runtime is $O(|E|\log|E|)$. The program is fixed before the graph and returns the two arc masks. A pair need not cover unused arcs of $H$; in the support-mixing application the edge count makes it a partition.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n and Fin m over the published arc-identity digraph, with every listed arc active; reason: enumeration preserves all finite graphs, parallel arcs and loops; it introduces no simplicity or connectivity promise
--   - encoding: an algorithm with a time bound → a finite program of the published integer RAM with actual instruction and copying costs, and logarithmic-width words; reason: the only uncharged optimization in the reduction is a correctly specified maximum-flow oracle; no arbitrary output function is assigned a cost
--   - encoding: O(|E| log |E|) runtime → ceil(K*(1+|E|*log(2+|E|))) with a uniform K; reason: the finite zero- and one-edge cases are included rather than invoking log 0 or a zero cost bound
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Theorem 3.2, p. 4 (PDF p. 4); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_IntegerReduction
import Definitions.Def_DirectedGlobalMincut_Sampling_RealRAM

namespace DirectedGlobalMincut.Sampling

/-- Theorem 3.2 (p.4): a uniform, oracle-free deterministic algorithm, including its runtime. -/
theorem theorem_3_2 :
    ∃ (P : IntegerProgram) (K : ℝ) (width : ℕ), 0 < K ∧ NoQueries P ∧ NoCoins P ∧
    ∀ n m (G : Graph n m) (r : Fin n), AllArcs G →
      let I := encGraphI G ++ [(r.val : ℤ)]
      let B := linearLogBudget K m m
      let z := CongruencyTU.run P CongruencyTU.noOracle CongruencyTU.noCoins I B
      CongruencyTU.isHalted P z = true ∧ z.cost ≤ B ∧
      WordBound P CongruencyTU.noOracle CongruencyTU.noCoins I B (n + m) width ∧
      ((∃ T₁ T₂, IsTree G r T₁ ∧ IsTree G r T₂ ∧ Disjoint T₁ T₂) →
        ∃ T₁ T₂, IsTree G r T₁ ∧ IsTree G r T₂ ∧ Disjoint T₁ T₂ ∧
          CongruencyTU.outputOf z =
            (List.ofFn (fun e => (if e ∈ T₁ then (1 : ℤ) else 0))) ++
            (List.ofFn (fun e => (if e ∈ T₂ then (1 : ℤ) else 0)))) := by sorry

end DirectedGlobalMincut.Sampling
