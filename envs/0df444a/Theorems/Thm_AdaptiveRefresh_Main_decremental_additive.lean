-- Prove2me | Theorems.Thm_AdaptiveRefresh_Main_decremental_additive
-- name    : AdaptiveRefresh.Main.decremental_additive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:02:43.414195+00:00
-- url     : https://prove2.me/theorems/6153599c-387f-4f6c-a907-cacc99dfa626
-- title:
--   Theorem 4.1 — decremental additive sparsification
-- statement:
--   Let $G$ be an unweighted loopless multigraph with $n$ labelled vertices, at most $m$ live identities, and initial maximum degree $\Delta$. For any $0<\eta<1/2$, there is a uniform costed causal randomized online program maintaining a nonnegative reweighted subgraph. Fix any polynomial horizon exponent $h$ and desired failure exponent $c>0$ before choosing the program and constants. For every measurable past-randomness-adaptive deletion strategy and every horizon $T\le(n+m+2)^h$, a common event of probability at least $1-\max(2,m)^{-c}$ includes termination, all completed outputs, and
--
--   $$\|L_H-L_G\|\le\eta\Delta,\qquad |H|\le10^4K n(1+\log\max(2,m))^2\eta^{-2},$$
--
--   where the amplification factor $K\ge1$ is a fixed natural number selected before all instances. Initialization has a uniform near-linear input bound; every prefix of update work has a uniform polynomial bound in $\log\max(2,m)$ and $\eta^{-1}$. The degree parameter never changes as edges are deleted.
--
--   The result covers disconnected and empty inputs and all clipping branches. The exact-real RAM has charged input access, arithmetic, comparisons, independent draws and ordinary memory; subset sampling and maintaining the output must be implemented in that machine.
--
--   Differences from the source:
--   - reading: η<1/2 → 0<η<1/2; reason: accuracy is implicitly positive in inverse-accuracy bounds
--   - reading: with high probability, with constant-factor amplification on printed p. 6 → every fixed h and c>0 choose code and constants before instances, with success at least 1-max(2,m)^(-c) on every horizon T≤(n+m+2)^h; reason: this is the disclosed finite polynomial-horizon interpretation, including independent randomized adversaries by conditioning
--   - encoding: Õ_η(n) size and the proof bound 10^4 nη^-2 log²m → 10^4 K nη^-2(1+log max(2,m))² with a uniform natural amplification factor K≥1; reason: the coefficient and accuracy/log exponents come from printed p. 13; constant-factor oversampling is authorized on printed p. 6 and padding covers the exact-storage branch
--   - encoding: poly(log m,η^-1) amortized work → a finite exact-real RAM and uniform positive resource constants with fixed natural work exponents; reason: each input read, memory operation, arithmetic/comparison, random draw and yield is charged; initialization is bounded independently of the future horizon
--   - encoding: H⊆G and the norm bound at all update times → one termination/support/size/accuracy/work event at initialization and every completed deletion, with Δ fixed initially; reason: this includes all clauses simultaneously and all disconnected, empty and clipped cases; no success or reduction guarantee is assumed
-- source:
--   Maximilian Probst Gutenberg, Yu-Cheng Yeh, Gernot Zöcklein, STOC 2027 submission #894 (October 2026), Theorem 4.1, printed p. 6 (PDF p. 7). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/894.pdf

import Mathlib
import Definitions.Def_AdaptiveRefresh_Main_OnlineMachine

set_option autoImplicit false
open MeasureTheory

namespace AdaptiveRefresh.Main

/-- Theorem 4.1, printed pp. 6,13 / PDF pp. 7,14. The graph may have parallel
identities and isolated vertices; Δ is the initial, never the current, maximum degree. -/
theorem decremental_additive (h : ℕ) (c : ℝ) (hc : 0 < c) :
    ∃ (K : ℕ) (P : OnlineProgram) (B : ResourceBounds),
      1 ≤ K ∧ PositiveBounds B ∧ B.sizeConstant = (10 ^ 4 : ℝ) * K ∧
      B.sizeLogExponent = 2 ∧ B.sizeAccuracyExponent = 2 ∧
      ∀ (n m T : ℕ) (η : ℝ) (G : Graph) (S : Strategy),
        0 < η → η < 1 / 2 → ValidGraph n G → G.length ≤ m →
        (∀ e ∈ G, e.weight = 1) → T ≤ (n + m + 2) ^ h → Measurable S →
        successLowerBound m c ≤ tapeLaw
          (Successful P B n m 0 T η G true S
            (fun G' H => opNorm (laplacian n H - laplacian n G') ≤
              η * initialMaxDegree n G)) := by sorry

end AdaptiveRefresh.Main
