-- Prove2me | Theorems.Thm_CollectiveDFS_path_basis
-- name    : CollectiveDFS.path_basis
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:07:40.803834+00:00
-- url     : https://prove2.me/theorems/a0fc9c1b-cb13-4ffc-994d-3cd91cce9cdf
-- title:
--   (7.11)–(7.12), p.23 — paths label an orthonormal basis of $\mathrm{DFS}_n(J)$
-- statement:
--   For $n\ge 1$ qubits, the joint eigenspaces of the partial Casimirs $(s^1)^2,\dots,(s^n)^2$ and $s_z$ form the path basis $|J_1,\dots,J_{n-1},J;m_J\rangle$:
--   1. for every path $(J_1,\dots,J_n)$ and every legal $m$ of its end spin $J_n$, the joint eigenspace with $(s^k)^2=J_k(J_k+1)$ for all $k$ and $s_z=m$ is a line;
--   2. the joint eigenspaces of distinct paths are orthogonal;
--   3. for legal $J$ and $m$, the lines of the paths ending at $J_n=J$ span $\mathrm{DFS}_n(J)$ at $m$.
--
--   In particular the paths ending at $J$ count the dimension of $\mathrm{DFS}_n(J)$; this is the basis in which the proof computes the action of exchange.
--
--   Differences from the source:
--   - encoding: half-integer labels J, m → doubled labels j2 = 2J : ℕ, m2 = 2m : ℤ; reason: exact half-integers; same instances
--   - encoding: basis vectors |J_1, …, J; m_J⟩ → the lines they span (joint eigenspaces); reason: the paper's vectors are fixed only up to a phase; one-dimensional, mutually orthogonal and spanning lines are exactly what a choice of unit vectors turns into an orthonormal basis
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eqs. (7.11)–(7.12), p.23

import Mathlib
import Definitions.Def_CollectiveDFS_dfs
import Definitions.Def_CollectiveDFS_LegalJ
import Definitions.Def_CollectiveDFS_LegalM
import Definitions.Def_CollectiveDFS_IsPath
import Definitions.Def_CollectiveDFS_pathSpace

open QAlgorithms

namespace CollectiveDFS

/-- Eqs. (7.11)–(7.12) (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII, p.23, PDF p.23): the eigenvalues `J_k(J_k+1)` of the commuting
`(s^k)²` label a basis `|J_1, J_2, …, J_{n−1}, J; m_J⟩`, and "the set of paths
`{J_1, …, J_n}` with fixed `J_n` counts the degeneracy of `DFS_n(J_n)`". For `n ≥ 1`:
(1) for every path and every legal `m` of its end spin, the joint eigenspace of the path is a line;
(2) the joint eigenspaces of distinct paths are orthogonal;
(3) for legal `J` and `m`, the joint eigenspaces of the paths ending at `J` span `DFS_n(J)` at `m`.

**Formalization Note** Paths are `p : Fin n → ℕ` with doubled labels, `p k = 2J_{k+1}`; the end
spin is `p (n−1)`. The basis vectors are unit vectors of these lines, fixed up to a phase; no
Clebsch–Gordan phase convention is imposed. -/
theorem path_basis (n : ℕ) (hn : 1 ≤ n) :
    (∀ p : Fin n → ℕ, IsPath p → ∀ m2 : ℤ, LegalM (p ⟨n - 1, by omega⟩) m2 →
      Module.finrank ℂ (pathSpace p m2) = 1) ∧
    (∀ p q : Fin n → ℕ, IsPath p → IsPath q → p ≠ q → ∀ m2 : ℤ,
      pathSpace p m2 ⟂ pathSpace q m2) ∧
    (∀ j2 : ℕ, LegalJ n j2 → ∀ m2 : ℤ, LegalM j2 m2 →
      (⨆ (p : Fin n → ℕ) (_ : IsPath p ∧ p ⟨n - 1, by omega⟩ = j2), pathSpace p m2) =
        dfs n j2 m2) := by sorry

end CollectiveDFS
