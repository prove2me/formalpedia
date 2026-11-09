-- Prove2me | Theorems.Thm_DirectedGlobalMincut_Sampling_theorem_4_4
-- name    : DirectedGlobalMincut.Sampling.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:58.875016+00:00
-- url     : https://prove2.me/theorems/4e70540f-d30a-4fb9-a62e-378462e95cc8
-- title:
--   Theorem 4.4 — Unbiased integral flow rounding with runtime
-- statement:
--   Let $H=(V,E,c)$ be a finite capacitated network, let $d:V\to\mathbb Z$ be its integer demand vector, and let $f:E\to\mathbb R$ be a nonnegative feasible flow satisfying $d$. One uniform randomized exact-arithmetic program outputs a nonnegative integral flow $\widehat f$ satisfying the same demands, with
--
--   $$\mathbb E[\widehat f_e]=f_e,\qquad
--   \lfloor f_e\rfloor\le\widehat f_e\le\lceil f_e\rceil\quad(e\in E).$$
--
--   Both rounding bounds and demand satisfaction hold on every supported output. The runtime is $O(|E|\log|V|)$, with no optimization oracle calls. The output is not required to obey the old fractional capacities. These guarantees allow rounding of the auxiliary flow without losing its projected connectivity property.
--
--   Differences from the source:
--   - encoding: finite vertex and arc sets → enumerated Fin n and Fin m over the published arc-identity digraph, with every listed arc active; reason: enumeration preserves all finite graphs, parallel arcs and loops; it introduces no simplicity or connectivity promise
--   - encoding: randomized rounding of an arbitrary nonnegative real input flow f → a finite exact-arithmetic RAM program with real Bernoulli sampling and a normalized PMF for its execution; reason: the real input flow is not narrowed to rational data; binding transition laws supplies fresh randomness and summability is required for every asserted mean
--   - encoding: O(|E| log |V|) runtime → a uniform bound ceil(K*(1+|E|*log(2+|V|))) for executed work; reason: the shift and additive constant complete empty and singleton sizes without changing the stated asymptotics
--   - encoding: the input flow network includes capacities → the program reads graph, demands and f; the theorem also quantifies over capacities certifying input feasibility; reason: rounding does not need to inspect capacities, and its output has no old-capacity restriction
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), Theorem 4.4, p. 10 (PDF p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_RealRAM

open scoped ENNReal

namespace DirectedGlobalMincut.Sampling

/-- Theorem 4.4 (p.10), including unbiasedness, both rounding bounds, demands and runtime. -/
theorem theorem_4_4 :
    ∃ (P : RealProgram) (K : ℝ), 0 < K ∧
    ∀ n m (G : Graph n m) (cap : Fin m → ℝ≥0∞) (d : Fin n → ℤ) (f : Fin m → ℝ),
      AllArcs G → FeasibleFlow (Network.mk G cap d) f →
      let H := Network.mk G cap d
      let I := encGraphR G ++ (List.ofFn (fun v => (d v : ℝ))) ++ List.ofFn f
      let B := linearLogBudget K n m
      let μ := realLaw P (fun _ => []) I B
      RealRuns P (fun _ => []) I B 0 0 ∧
      (∀ s ∈ μ.support, (realOutput s).length = m ∧
        DemandFlow H (fun e => s.reg (e.val + 1)) ∧
        ∀ e : Fin m, (∃ z : ℤ, s.reg (e.val + 1) = z) ∧
          (⌊f e⌋ : ℝ) ≤ s.reg (e.val + 1) ∧ s.reg (e.val + 1) ≤ (⌈f e⌉ : ℝ)) ∧
      ∀ e : Fin m, HasMean μ (fun s => s.reg (e.val + 1)) ∧
        Mean μ (fun s => s.reg (e.val + 1)) = f e := by sorry

end DirectedGlobalMincut.Sampling
