-- Prove2me | Theorems.Thm_CollectiveDFS_casimir_eq_exchange
-- name    : CollectiveDFS.casimir_eq_exchange
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:03:50.732287+00:00
-- url     : https://prove2.me/theorems/4b82cf7a-9594-408f-bcc7-bbd3987f4fa4
-- title:
--   (7.23), p.26 — the partial Casimirs are sums of exchanges
-- statement:
--   For $1\le k\le n$,
--   $$(s^k)^2=k\Big(1-\frac k4\Big)I+\frac12\sum_{\substack{i\neq j\\ 1\le i,j\le k}}E_{ij},$$
--   where the sum runs over ordered pairs of distinct qubits among the first $k$, so each exchange appears twice. For example $(s^1)^2=\tfrac34 I$ and $(s^2)^2=I+E_{12}$.
--
--   Thus every $(s^k)^2$ is a Hamiltonian at the disposal of the exchange-only model, up to the identity.
--
--   Differences from the source:
--   - encoding: qubits 1, …, n; |0⟩, |1⟩ → 0-based wires Fin n; Bool basis with false = |0⟩; reason: Lean convention; same operators
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eq. (7.23), p.26

import Mathlib
import Definitions.Def_CollectiveDFS_exchange
import Definitions.Def_CollectiveDFS_partialCasimir

open QAlgorithms

namespace CollectiveDFS

/-- Eq. (7.23) (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII.D, p.26, PDF p.26): for `1 ≤ k ≤ n`,
`(s^k)² = k(1 − k/4) I + ½ Σ_{i≠j=1}^k E_ij`, the sum over ordered pairs of distinct qubits among
the first `k`.

**Formalization Note** The sum runs over ordered pairs `(i, j)` of 0-based wires with
`i, j < k` and `i ≠ j`, so each swap appears twice, as in (7.23) (at `k = 2` the formula gives
`I + E₁₂`, eigenvalues `2` and `0`). `(s^k)²` is `partialCasimir n k`. -/
theorem casimir_eq_exchange (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    partialCasimir n k =
      ((k : ℂ) * (1 - (k : ℂ) / 4)) • (1 : Matrix (Qubits n) (Qubits n) ℂ) +
        (1 / 2 : ℂ) • ∑ q ∈ Finset.univ.filter
          (fun q : Fin n × Fin n => (q.1 : ℕ) < k ∧ (q.2 : ℕ) < k ∧ q.1 ≠ q.2),
          exchange q.1 q.2 := by sorry

end CollectiveDFS
