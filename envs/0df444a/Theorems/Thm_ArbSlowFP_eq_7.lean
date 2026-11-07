-- Prove2me | Theorems.Thm_ArbSlowFP_eq_7
-- name    : ArbSlowFP.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:46:45.044146+00:00
-- url     : https://prove2.me/theorems/2bb3a4fe-b23c-4744-8693-a3b91c1e4477
-- title:
--   (7) — the height of the process (6) is nondecreasing
-- statement:
--   Let $A\in\mathbb Q^{m\times m}$ be skew-symmetric and let $(u_t)$ be the score states of the auxiliary process. Since $A_{ii}=0$, playing a maximizing action leaves its own score unchanged, so
--   $$H_{t+1}\ge H_t\qquad(t\ge0).$$
--
--   Differences from the source:
--   - generalization: the process (6) under a total priority order ≺ → every sequence i with IsPriorityRun for an arbitrary rank function (not required injective); reason: (7) uses only that i_t maximizes u_t; an injective rank, which encodes ≺, is an instance
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.13, eq. (7)

import Mathlib
import Definitions.Def_ArbSlowFP_ValidFrom

open Matrix

namespace ArbSlowFP

/-- Eq. (7), p.13 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…): since `A_ii = 0`,
playing a maximizing action leaves its own score unchanged, so `H_{t+1} ≥ H_t` along the process (6). -/
theorem eq_7 {ι : Type*} [Fintype ι] [Nonempty ι] (A : Matrix ι ι ℚ) (hA : Aᵀ = -A)
    (rank : ι → ℕ) (f : ι → ℚ) (i : ℕ → ι) (hi : IsPriorityRun A rank f i) (t : ℕ) :
    height (procScore A f i t) ≤ height (procScore A f i (t + 1)) := by sorry

end ArbSlowFP
