-- Prove2me | Theorems.Thm_CollectiveDFS_dfs_finrank
-- name    : CollectiveDFS.dfs_finrank
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:07:10.24349+00:00
-- url     : https://prove2.me/theorems/ca081d01-d2ce-46db-bcd0-b4ca48a406c2
-- title:
--   (7.2)–(7.3), p.20 — decomposition into spin sectors and $\dim\mathrm{DFS}_n(J)=n_J$
-- statement:
--   For $n$ qubits, the decomposition $H_S\cong\bigoplus_J\mathbb C^{n_J}\otimes\mathbb C^{2J+1}$ of (7.2) holds with
--   $$n_J=\frac{(2J+1)\,n!}{(n/2+J+1)!\,(n/2-J)!}\tag{7.3}$$
--   in the following sense:
--   1. for every legal $J$ and legal $m$, $\dim\mathrm{DFS}_n(J)=n_J$ at magnetic number $m$;
--   2. the sectors $W_J$ of distinct legal $J$ are orthogonal;
--   3. the sectors $W_J$ of the legal $J$ span the whole space;
--   4. eigenspaces of $s_z$ for distinct $m$ are orthogonal;
--   5. each $W_J$ is spanned by the $\mathrm{DFS}_n(J)$ at its legal $m$.
--
--   It fixes the size of the target algebra $\mathfrak{su}(n_J)$ of Theorem 5 and shows the DFSs are not empty.
--
--   Differences from the source:
--   - encoding: half-integer labels J, m → doubled labels j2 = 2J : ℕ, m2 = 2m : ℤ; reason: exact half-integers; same instances
--   - encoding: n_J as a quotient of factorials → the identity n_J · ((n + j2)/2 + 1)! · ((n − j2)/2)! = (j2 + 1) · n!; reason: the division is exact; no truncated division
--   - reading: H_S ≅ ⊕_J C^{n_J} ⊗ C^{2J+1} → the sectors W_J are orthogonal and span H_S, each W_J is spanned by its DFSs at the legal m, distinct s_z-eigenspaces are orthogonal, and each DFS has dimension n_J; reason: this is the concrete content of the isomorphism: W_J is the orthogonal sum of 2J + 1 copies of C^{n_J}
--   - generalization: n ≥ 1 qubits → any n : ℕ, including n = 0; reason: at n = 0 every clause holds (a one-dimensional space with J = 0 and n_0 = 1), and the statement specializes to n ≥ 1
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eqs. (7.2)–(7.3), p.20

import Mathlib
import Definitions.Def_CollectiveDFS_dfs
import Definitions.Def_CollectiveDFS_LegalJ
import Definitions.Def_CollectiveDFS_LegalM

open QAlgorithms

namespace CollectiveDFS

/-- Eqs. (7.2)–(7.3) (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII, p.20, PDF p.20): the `n`-qubit space decomposes as
`H_S ≅ ⊕_{J} C^{n_J} ⊗ C^{2J+1}`, and the degeneracy of spin `J` is
`n_J = (2J + 1) n! / ((n/2 + J + 1)! (n/2 − J)!)`. Concretely:
(1) for legal `J` and `m`, `dim DFS_n(J) = n_J`, written as `n_J (n/2+J+1)! (n/2−J)! = (2J+1) n!`;
(2) the spin sectors `W_J` of distinct legal `J` are orthogonal;
(3) they span the whole space;
(4) distinct `s_z`-eigenspaces are orthogonal;
(5) each `W_J` is spanned by its `DFS_n(J)` at the legal `m`.

**Formalization Note** Doubled labels `j2 = 2J`, `m2 = 2m`: `n/2 + J = (n + j2)/2` and
`n/2 − J = (n − j2)/2`, exact in `ℕ` because `j2 ≡ n (mod 2)` and `j2 ≤ n`; the degeneracy formula
is stated multiplied out, so no division is involved. Any `n`, including `n = 0`. -/
theorem dfs_finrank (n : ℕ) :
    (∀ j2 : ℕ, LegalJ n j2 → ∀ m2 : ℤ, LegalM j2 m2 →
      Module.finrank ℂ (dfs n j2 m2) * (((n + j2) / 2 + 1).factorial * ((n - j2) / 2).factorial) =
        (j2 + 1) * n.factorial) ∧
    (∀ j2 j2' : ℕ, LegalJ n j2 → LegalJ n j2' → j2 ≠ j2' →
      spinSector n j2 ⟂ spinSector n j2') ∧
    (⨆ (j2 : ℕ) (_ : LegalJ n j2), spinSector n j2) = ⊤ ∧
    (∀ m2 m2' : ℤ, m2 ≠ m2' → szEigenspace n m2 ⟂ szEigenspace n m2') ∧
    (∀ j2 : ℕ, LegalJ n j2 → (⨆ (m2 : ℤ) (_ : LegalM j2 m2), dfs n j2 m2) = spinSector n j2) := by sorry

end CollectiveDFS
