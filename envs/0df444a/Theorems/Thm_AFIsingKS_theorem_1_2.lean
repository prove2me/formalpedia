-- Prove2me | Theorems.Thm_AFIsingKS_theorem_1_2
-- name    : AFIsingKS.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T10:15:00.03832+00:00
-- url     : https://prove2.me/theorems/e4482f92-e993-47c4-9a40-21d7bae5fc2c
-- title:
--   Theorem 1.2 — random $d$-regular graphs have no Ising zeros near $[0,(1-\delta)\beta_{\mathrm{KS}}(d)]$
-- statement:
--   Let $d\ge3$ be an integer and $0<\delta<1$. Let $\beta_{\mathrm{KS}}(d)=2\operatorname{arctanh}(1/\sqrt{d-1})$ be the Kesten–Stigum threshold. For a graph $G$ on $n$ vertices let $\mathcal H_G(\sigma)$ be the number of edges cut by $\sigma\in\{\pm1\}^n$, and $Z_G(\beta)=\sum_\sigma\exp(\beta\mathcal H_G(\sigma))$ the Ising partition function. There exists $\eta=\eta(d,\delta)>0$ such that with probability at least $1-o_n(1)$ over the uniformly random $d$-regular graph $G$, the partition function has no zeros in the strip
--   $$\{\beta\in\mathbb C:\operatorname{dist}(\beta,[0,(1-\delta)\beta_{\mathrm{KS}}(d)])<\eta\}.$$
--
--   This is the main technical result of the paper. Through Barvinok's interpolation method it yields a polynomial-time approximate counting algorithm for the antiferromagnetic Ising model on random regular graphs up to the Kesten–Stigum threshold.
--
--   Differences from the source:
--   - encoding: hypothesis "0 ≤ β ≤ (1 − δ)·β_KS(d)" before ∃η, with β re-bound in the conclusion → the hypothesis is omitted; reason: η = η(d, δ) does not depend on it, and the interval is nonempty since δ < 1
--   - encoding: spins ±1 → spins `Fin n → Bool`, `true` for +1; reason: same objects
--   - encoding: with probability at least 1 − o_n(1) → `PottsRapidMixing.WithHighProb`: the uniform probability on simple d-regular graphs on `Fin n` tends to 1 along n with n * d even; reason: such graphs exist only for nd even
-- source:
--   Bencs, Huang, Lee, Liu, Regts, On Zeros and Algorithms for Disordered Systems II, arXiv:2610.40598 (held version, sha256 2a07c158…), Theorem 1.2, p.4

import Mathlib
import Definitions.Def_AFIsingKS_betaKS
import Definitions.Def_AFIsingKS_partitionFn
import Definitions.Def_PottsRapidMixing_Ensemble

open scoped Classical
open Set Filter Topology

namespace AFIsingKS

/-- Theorem 1.2 (Bencs, Huang, Lee, Liu, Regts, arXiv:2610.40598 (held version, sha256 2a07c158…), p.4): with probability `1 − o_n(1)` over the uniformly random `d`-regular graph, the Ising
partition function has no zeros in the strip `{β ∈ ℂ : dist(β, [0, (1 − δ) β_KS(d)]) < η}`.

**Formalization Note.** The printed hypothesis `0 ≤ β ≤ (1 − δ) β_KS(d)` names a `β` that is re-bound in the conclusion, and
`η = η(d, δ)` does not depend on it, so it is omitted. The segment is nonempty since `δ < 1` and `β_KS(d) > 0`, so
`Metric.infDist` is the genuine distance. The probability is over simple `d`-regular graphs on `Fin n`, not over the
configuration model. -/
theorem theorem_1_2 (d : ℕ) (hd : 3 ≤ d) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ η : ℝ, 0 < η ∧ PottsRapidMixing.WithHighProb d (fun _ G => ∀ β : ℂ,
      Metric.infDist β ((fun x : ℝ => (x : ℂ)) '' Icc 0 ((1 - δ) * betaKS d)) < η →
        partitionFn G β ≠ 0) := by sorry

end AFIsingKS
