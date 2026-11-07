-- Prove2me | Theorems.Thm_CompPermOracle_eq_31
-- name    : CompPermOracle.eq_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:27.865805+00:00
-- url     : https://prove2.me/theorems/8d6723b0-2c88-4dde-987c-c3f03f9aacb2
-- title:
--   Eq. (31), proof of Theorem 4.2 — the hybrid bound between the compressed and the purified state
-- statement:
--   Let $N\ge3$ and $3q-1\le N$. For a query algorithm $A$, let $\psi^{\mathrm{cpO}}_q$ be its compressed state and $\psi^{P}_q$ its purified state after $q$ queries. Then
--   $$
--   \big\|\psi^{\mathrm{cpO}}_q-(I\otimes\tilde V)\psi^{P}_q\big\|\le\frac{60q}{\sqrt{N-q+1}}+\frac{q(q+1)}{2(N-2q+1)}.
--   $$
--   Comparison of acceptance probabilities follows from this distance, and §5 of the source uses it directly.
--
--   Differences from the source:
--   - generalization: q forward and inverse queries → oracle steps coherently controlled on a direction bit; reason: a fixed schedule is the case where the algorithm sets the bit classically
--   - reading: (31) within the proof of Theorem 4.2 → explicit hypothesis $N\ge3$; reason: the hypothesis of the theorem whose proof contains (31), and of the bound (12) it sums
--   - encoding: $3q-1\le N$ → `3 * q ≤ N + 1`; reason: no truncated subtraction
--   - encoding: $[N]=\{1,\dots,N\}$, blank symbol $\bot$ → `Fin N` (0-based), $\bot$ = `none`; reason: a relabelling; no index appears in the bound
-- source:
--   Carolan, Majenz, Compressed Permutation Oracles Revisited, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), proof of Theorem 4.2, eq. (31), p.17

import Mathlib
import Definitions.Def_CompPermOracle_opTensor
import Definitions.Def_CompPermOracle_PartialPerm
import Definitions.Def_CompPermOracle_swapOp
import Definitions.Def_CompPermOracle_cpO
import Definitions.Def_CompPermOracle_Levels
import Definitions.Def_CompPermOracle_Alg

namespace CompPermOracle

/-- Proof of Theorem 4.2, eq. (31) (Carolan, Majenz, arXiv:2609.28469 (version of 2026-11-03, sha256 52ebc507…), p.17): the Euclidean distance after `q` queries
between the compressed state and the image under `Ṽ` of the purified state.

**Formalization Note.** `3q − 1 ≤ N` is `3q ≤ N + 1`. `N ≥ 3` is the hypothesis of Theorem 4.2, inside
whose proof (31) is stated. -/
theorem eq_31 {N q : ℕ} {W : Type} [Fintype W] [DecidableEq W] (hN : 3 ≤ N) (hq : 3 * q ≤ N + 1)
    (A : Alg N W) :
    ‖compressedState A q -
        opTensor (1 : Hil (Acc N W) →L[ℂ] Hil (Acc N W)) (Vtmap N) (purifiedState A q)‖ ≤
      60 * (q : ℝ) / Real.sqrt ((N : ℝ) - q + 1) +
        (q : ℝ) * ((q : ℝ) + 1) / (2 * ((N : ℝ) - 2 * q + 1)) := by sorry

end CompPermOracle
