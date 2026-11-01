-- Prove2me | Theorems.Thm_CollectiveDFS_special_top_sector
-- name    : CollectiveDFS.special_top_sector
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:08:53.046528+00:00
-- url     : https://prove2.me/theorems/1bc64ff5-9c31-45c4-b208-3710bf457c79
-- title:
--   Special case $J=n/2-1$, p.28 — $\mathfrak{su}(n-1)$ on $\mathrm{DFS}_n(n/2-1)$
-- statement:
--   Let $n\ge 5$. Assume exchange acts as $\mathfrak{su}$ independently on every $\mathrm{DFS}_{n-1}(J')$, and on $\mathrm{DFS}_n(n/2-2)$ at every legal $m$. Then
--   1. $\dim\mathrm{DFS}_n(n/2-1)=n-1$ at every legal $m$, and
--   2. exchange acts as $\mathfrak{su}$ independently on $\mathrm{DFS}_n(n/2-1)$ at every legal $m$.
--
--   This is the case the main induction step leaves out, because $\mathrm{DFS}_n(n/2-1)$ has no TT state.
--
--   Differences from the source:
--   - reading: induction hypothesis: su(n_J) on each DFS_{n−1}(J) independently using only exchange operators and the identity Hamiltonian → SectorUniversal (n − 1): exchange alone, traceless elements of H^{n−1}_J; reason: Theorem 5, which the induction proves, is stated for exchange alone; su elements are traceless, so the identity Hamiltonian contributes nothing to them
--   - generalization: DFS_n(n/2 − 2) and DFS_n(n/2 − 1) at a fixed m_J → every legal magnetic number; reason: exchange commutes with the S_α; the fixed-m statement is a special case
--   - encoding: half-integer labels J, m → doubled labels j2 = 2J : ℕ, m2 = 2m : ℤ; reason: exact half-integers; same instances
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, special case J = n/2 − 1, §VII.D.3, p.28

import Mathlib
import Definitions.Def_CollectiveDFS_SectorUniversal

open QAlgorithms

namespace CollectiveDFS

/-- The special case `J = n/2 − 1` of the proof of Theorem 5 (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII.D.3, p.28, PDF p.28):
"The dimension of this DFS is n − 1. We now show how to perform su(n − 1) on this DFS using the
fact that we have already established su(n_{J=n/2−2}) on DFS_n(n/2 − 2)." For `n ≥ 5`, if
exchange acts as `su` independently on every `DFS_{n−1}` and on `DFS_n(n/2 − 2)` (every legal
`m`), then `dim DFS_n(n/2 − 1) = n − 1` and exchange acts as `su` independently on
`DFS_n(n/2 − 1)` (every legal `m`).

**Formalization Note** Doubled labels: `J = n/2 − 1` and `n/2 − 2` are `n − 2` and `n − 4` (no
truncation since `n ≥ 5`). -/
theorem special_top_sector (n : ℕ) (hn : 5 ≤ n) (hind : SectorUniversal (n - 1))
    (hbelow : ∀ m2 : ℤ, LegalM (n - 4) m2 → ReachesSu n (n - 4) m2) :
    (∀ m2 : ℤ, LegalM (n - 2) m2 → Module.finrank ℂ (dfs n (n - 2) m2) = n - 1) ∧
    (∀ m2 : ℤ, LegalM (n - 2) m2 → ReachesSu n (n - 2) m2) := by sorry

end CollectiveDFS
