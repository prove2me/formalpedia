-- Prove2me | Theorems.Thm_DQIShattered_Supplement_theorem_4_6
-- name    : DQIShattered.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T04:36:14.590191+00:00
-- url     : https://prove2.me/theorems/f90bb3aa-bfbd-4540-9e88-5a104cb924b8
-- title:
--   Theorem 4.6 — Shattering in Max-XORSAT
-- statement:
--   There is an $\varepsilon_0>0$ such that, for every $\varepsilon\in(0,\varepsilon_0)$ and every $(k,D,\beta)$ satisfying all hypotheses of Theorem 4.3, the Gibbs measure of $H\sim\mathbb G_{\mathrm{ER}}(N,k,D)$ is $(\varepsilon/k)$-shattered. More explicitly, a single constant $c>0$, independent of $N$, gives with probability at least $1-e^{-cN}$ for all sufficiently large $N$ nonempty clusters whose individual masses are at most $e^{-cN}$, Hamming diameters are at most $(\varepsilon/k)N$, pairwise separations are at least $(\varepsilon/k)^3N$, and whose union has mass at least $1-e^{-cN}$.
--
--   Differences from the source:
--   - reading: the hypotheses of Theorem 4.3 are incorporated by reference → Lean inlines “sufficiently small” $\varepsilon$, $k\ge k_0(\varepsilon)$, $D\ge k$, and the full interval (4.4); reason: the platform theorem must stand on its own
--   - generalization: the Gibbs measure is $(\varepsilon/k)$-shattered with high probability → Lean retains the stronger probability $1-e^{-cN}$ for all sufficiently large $N$; reason: Propositions 5.9–5.11 prove an exponentially-good bound
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 4.6, p.19; proof pp.28–30

import Mathlib
import Definitions.Def_DQIShattered_Supplement_Framework

namespace DQIShattered

namespace Supplement

/-- **Theorem 4.6 (Shattering in Max-XORSAT).**
Zhou, Shutty, Sellke, Jordan, arXiv:2609.40345, held version sha256 0c7f6fdf…,
p.19.

Under every hypothesis of Theorem 4.3, the Gibbs measure is `(ε/k)`-shattered. The conclusion
keeps the exponentially good probability proved by Propositions 5.9–5.11: one fixed `c > 0`
controls both the exceptional probability and all four cluster clauses for all sufficiently
large `N`. -/
theorem theorem_4_6 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ∀ D : ℝ, (k : ℝ) ≤ D → ∀ β : ℝ, InHardRange k D ε β →
          IsExponentiallyShattered k D β (ε / k) := by sorry

end Supplement

end DQIShattered
