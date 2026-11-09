-- Prove2me | Theorems.Thm_CEPolytopeHard_variance_entropy_bound
-- name    : CEPolytopeHard.variance_entropy_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:18:36.052366+00:00
-- url     : https://prove2.me/theorems/bf29ba03-35f7-4df4-989b-9ef67b57a859
-- title:
--   Section 3.2 — $V(t) - V(s) \le 2(h(t) - h(s))$
-- statement:
--   Let $P$ be a stochastic $k\times k$ matrix with stationary distribution $\mu$, let $x_1, \dots, x_k \in [0,1]^d$, and let $0 < t < s \le 1$. Then
--   $$
--   V(t) - V(s) \le 2\big(h(t) - h(s)\big),
--   $$
--   where $V$ is the averaged conditional variance (normalized norm) and $h$ the average entropy of the rows of $P(\cdot)$.
--
--   The drop of the conditional variance between two scales is controlled by the drop of entropy, which Lemma 3.7 makes small at some scale.
--
--   Differences from the source:
--   - generalization: the points of one layer of a fixed set of the lift g, with its chain → arbitrary points in [0, 1]^d and any stochastic P with stationary µ; reason: the argument uses only these properties
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 3.2, Eq. (10) and the display following it, p.17

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_CEPolytopeHard_hEnt
import Definitions.Def_CEPolytopeHard_condVar

set_option autoImplicit false

namespace CEPolytopeHard

/-- **The variance drop is bounded by the entropy drop** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, Section 3.2, p.17: "Now set
K := K(t, s). Then x̄_i(t) = E_{j∼P_i(t)} x_j = E_{a∼K_i,j∼P_a(s)} x_j = E_{j∼K_i} x̄_j(s). (10)
Therefore, V(t) − V(s) = … ≤ 2 E_{i∼μ,j∼K_i} d_KL(P_j(s)∥P_i(t)) = 2(h(t) − h(s))").

For every stochastic `k × k` matrix `P` with stationary distribution `μ`, all points
`x_1, …, x_k ∈ [0, 1]^ι` and `0 < t < s ≤ 1`: `V(t) − V(s) ≤ 2(h(t) − h(s))`.

**Formalization Note** `V` uses the normalized norm (p.9) and `h` natural logarithms. The paper
states the bound for the points of one layer of a fixed set; here the points are arbitrary in
`[0, 1]^ι`. -/
theorem variance_entropy_bound {k : ℕ} {ι : Type} [Fintype ι] (P : Matrix (Fin k) (Fin k) ℝ)
    (hP : IsStochastic P) (μ : Fin k → ℝ) (hμ : IsStationary P μ) (x : Fin k → ι → ℝ)
    (hx : ∀ j, x j ∈ Set.Icc (0 : ι → ℝ) 1) (t s : ℝ) (ht : 0 < t) (hts : t < s) (hs : s ≤ 1) :
    condVar P μ x t - condVar P μ x s ≤ 2 * (hEnt P μ t - hEnt P μ s) := by sorry

end CEPolytopeHard
