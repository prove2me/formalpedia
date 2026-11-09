-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_theorem_2_1
-- name    : DirectedGlobalMincut.Sampling.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:48.287013+00:00
-- url     : https://prove2.me/theorems/fbd13de6-3850-4015-b795-120bb95716b9
-- title:
--   Theorem 2.1 — Recover a rooted cut from a tree
-- statement:
--   On the source's positive integral, polynomially bounded input domain, let $T$ be a spanning out-arborescence rooted at $r$. One deterministic maximum-flow oracle program returns a valid rooted cut $S$. If $T$ 1-respects some rooted minimum cut, then
--
--   $$S\text{ is a rooted minimum cut}.$$
--
--   The program uses $O(\log n)$ maximum-flow computations, each on an $O(m)$-size graph, and near-linear additional work. The success condition is an implication about the returned cut, not a promise that the supplied tree already respects an optimum. Without that condition the returned cut is still valid.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n and Fin m over the published arc-identity digraph, with every listed arc active; reason: enumeration preserves all finite graphs, parallel arcs and loops; it introduces no simplicity or connectivity promise
--   - encoding: an algorithm with a time bound → a finite program of the published integer RAM with actual instruction and copying costs, and logarithmic-width words; reason: the only uncharged optimization in the reduction is a correctly specified maximum-flow oracle; no arbitrary output function is assigned a cost
--   - reading: O(log n) calls, O(m)-size graphs and soft-O(m) overhead → uniform constants before the input, individual query-volume bound ceil(K*m), call bound ceil(K*log(2+n)), and ceil(K*m*log(2+n)^k) overhead; reason: the logarithmic exponent for overhead is not specified by the source; capacities can be integral and polynomially encoded by the stated scaling conventions
--   - encoding: a cut separating distinct vertices, or a nonempty root-excluding cut → the input domain requires n>=2; reason: below two vertices the claimed cut does not exist; this excludes only undefined cut instances
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Theorem 2.1, p. 2 (PDF p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_IntegerReduction

namespace DirectedGlobalMincut.Sampling

/-- Theorem 2.1 (p.2): valid cuts always, exact recovery when a rooted optimum is 1-respected. -/
theorem theorem_2_1 :
    ∀ b : ℕ, 1 ≤ b →
    ∃ (P : IntegerProgram) (K : ℝ) (k width exponent : ℕ), 0 < K ∧ NoCoins P ∧
    ∀ n m (G : Graph n m) W w (r : Fin n) (T : Finset (Fin m)),
      InputDomain b G W w → IsTree G r T →
      let I := encGlobal G W w ++ [(r.val : ℤ)] ++
        List.ofFn (fun e => (if e ∈ T then (1 : ℤ) else 0))
      let B := reductionClock K k n m
      ∀ O, IsMFOracleI O →
        let z := CongruencyTU.run P O CongruencyTU.noCoins I B
        CongruencyTU.isHalted P z = true ∧ z.cost ≤ B ∧
        z.queries ≤ ⌈K * Real.log (2 + n)⌉₊ ∧
        WordBound P O CongruencyTU.noCoins I B n width ∧
        IntegralQuestions P O CongruencyTU.noCoins I B exponent ∧
        (∀ t < B, ∀ xs, CongruencyTU.queryAt P O CongruencyTU.noCoins I t = some xs →
          queryVolumeI xs ≤ ⌈K * m⌉₊) ∧
        ∃ S, IsRootedCut r S ∧ CongruencyTU.outputOf z = cutEncoding S ∧
          ((∃ U, IsRootedMinimum G (fun e => (w e : ℝ)) r U ∧ OneRespects G T U) →
            IsRootedMinimum G (fun e => (w e : ℝ)) r S) := by sorry

end DirectedGlobalMincut.Sampling
