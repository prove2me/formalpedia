-- Prove2me | Theorems.Thm_ExactParallelSampling_QuasiUniform_theorem_6_3
-- name    : ExactParallelSampling.QuasiUniform.theorem_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T20:51:53.774123+00:00
-- url     : https://prove2.me/theorems/576194aa-5f47-4f70-a0b1-64950d6e9240
-- title:
--   Theorem 6.3 — density preservation under a uniformly random m-subset (KPS26a, Theorem 4.1)
-- statement:
--   Let $i\le m\le N$ be integers and $\mathcal F\subseteq\binom{[N]}{i}$, with $p=|\mathcal F|/\binom Ni$. If $S'$ is a uniformly random $m$-subset of $[N]$, then
--   $$\Pr_{S'}\Big[\big|\mathcal F\cap\tbinom{S'}{i}\big|\ge\frac p2\binom mi\Big]\ge\frac14\cdot2^{-2\frac{N-m}{N-i}\log(1/p)} .$$
--   The right-hand side is defined for $i<N$ and $p>0$, the only cases in which the source applies the theorem. At the boundary it is extended continuously: it is $1/4$ when $m=N$ (which includes $i=N$), and $0$ when $p=0$ and $m<N$. In both boundary cases the event on the left has probability $1$.
--
--   Differences from the source:
--   - encoding: the right-hand side, defined for i < N and p > 0 → if m = N then 1/4, else if p = 0 then 0, else the printed formula; reason: the source applies the theorem only where the formula is defined (p. 31); these values are its continuous extension (at m = N the exponent is 0; as p → 0 with m < N it tends to 0), and on the defined domain the Lean bound is the printed one
--   - encoding: [N] and F ∩ (S′ choose i) → Fin N and the members of F contained in S′; reason: every member of F has i elements
--   - encoding: probabilities over uniformly random finite objects → uprob: the number of favourable outcomes divided by the number of outcomes; reason: this is the uniform distribution on a finite set
-- source:
--   Shen, Li, Shi and Li (2026), Exact Parallel Sampling without Maximal Independent Sets, supplied PDF, Theorem 6.3, p. 31; SHA256 34a681c96bb71642376464cc79acf05535f33206b14e5949999f5f31c28082d4

import Mathlib
import Definitions.Def_ExactParallelSampling_QuasiUniform_IndepSystems

noncomputable section
open Classical

namespace ExactParallelSampling.QuasiUniform

/-- **Theorem 6.3 (Density preservation, [KPS26a, Theorem 4.1])**, Shen, Li, Shi and Li (2026),
p. 31. Let `i ≤ m ≤ N` be integers and `F ⊆ ([N] choose i)` with `p = |F| / (N choose i)`. If `S'`
is a uniformly random `m`-subset of `[N]`, then
`Pr_{S'}[|F ∩ (S' choose i)| ≥ (p/2)(m choose i)] ≥ (1/4) · 2^{−2 ((N−m)/(N−i)) log(1/p)}`.
The right-hand side is defined for `i < N` and `p > 0`; it is extended continuously to the
boundary: `1/4` when `m = N` (in particular when `i = N`), and `0` when `p = 0` and `m < N`. -/
theorem theorem_6_3 (i m N : ℕ) (him : i ≤ m) (hmN : m ≤ N) (F : Finset (Finset (Fin N)))
    (hF : ∀ A ∈ F, A.card = i) :
    let pF : ℝ := (F.card : ℝ) / (N.choose i : ℝ)
    (if m = N then (1 / 4 : ℝ)
      else if pF = 0 then 0
      else 1 / 4 * (2 : ℝ) ^ (-2 * (((N - m : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)) *
        Real.logb 2 (1 / pF))) ≤
      uprob {S' // S' ∈ (Finset.univ : Finset (Fin N)).powersetCard m}
        (fun S' => pF / 2 * (m.choose i : ℝ) ≤ ((F.filter (fun A => A ⊆ S'.1)).card : ℝ)) := by sorry

end ExactParallelSampling.QuasiUniform
