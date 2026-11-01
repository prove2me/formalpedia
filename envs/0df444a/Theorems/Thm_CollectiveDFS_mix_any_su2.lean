-- Prove2me | Theorems.Thm_CollectiveDFS_mix_any_su2
-- name    : CollectiveDFS.mix_any_su2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:09:08.070241+00:00
-- url     : https://prove2.me/theorems/ce00ec85-c0a6-4fa3-985b-1f2dff20d58b
-- title:
--   (7.31), pp.27–28 — $\mathfrak{su}(2)$ between any T-state and any B-state
-- statement:
--   Assume exchange acts as $\mathfrak{su}$ independently on every $\mathrm{DFS}_{n-1}(J')$, and let $0<J<n/2-1$. Let $i$ be a unit B-state and $i'$ a unit T-state of $\mathrm{DFS}_n(J)$ at a common magnetic number $m$: $i$ lies in the eigenspace of $(s^{n-1})^2$ for $J_{n-1}=J-\tfrac12$ and $i'$ in that for $J_{n-1}=J+\tfrac12$. Then there are $X,Y,Z\in H^n_J$ acting on $\mathrm{DFS}_n(J)$ at $m$ as
--   $$X=|i\rangle\langle i'|+|i'\rangle\langle i|,\qquad Y=i\big(|i\rangle\langle i'|-|i'\rangle\langle i|\big),\qquad Z=|i\rangle\langle i|-|i'\rangle\langle i'|.$$
--
--   This is Step 2 of the proof: every $\mathfrak{su}(2)$ between a T- and a B-state is available, independently on $\mathrm{DFS}_n(J)$.
--
--   Differences from the source:
--   - generalization: m_J fixed (m_J = J in the proof) → every legal magnetic number m; reason: exchange commutes with the S_α (fact (i), (7.13)); the statement at m = J is a special case
--   - reading: induction hypothesis: su(n_J) on each DFS_{n−1}(J) independently using only exchange operators and the identity Hamiltonian → SectorUniversal (n − 1): exchange alone, traceless elements of H^{n−1}_J; reason: Theorem 5, which the induction proves, is stated for exchange alone; su elements are traceless, so the identity Hamiltonian contributes nothing to them
--   - encoding: 0 < J < n/2 − 1 → 2J = jB + 1 with jB + 3 < n; B-states with label jB, T-states with jB + 2; reason: avoids natural-number subtraction
--   - encoding: qubits 1, …, n; |0⟩, |1⟩ → 0-based wires Fin n; Bool basis with false = |0⟩; reason: Lean convention; same operators
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eq. (7.31) and the paragraph after it, pp.27–28

import Mathlib
import Definitions.Def_CollectiveDFS_SectorUniversal

open QAlgorithms

namespace CollectiveDFS

/-- Step 2 of the proof of Theorem 5, eq. (7.31) (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII.D.2, pp.27–28, PDF pp.27–28): "one
can implement every su(2) between any two T- and B-states in DFS_n(J). Each of these su(2)
operations is performed independently on DFS_n(J)." Assume exchange acts as `su` independently on
every `DFS_{n−1}`, and `0 < J < n/2 − 1`. Let `i` be a unit B-state of `DFS_n(J)` (eigenvalue of
`(s^{n−1})²` for `J_{n−1} = J − ½`) and `i′` a unit T-state of `DFS_n(J)` (for `J_{n−1} = J + ½`),
at a common magnetic number. Then there are `X, Y, Z ∈ H^n_J` acting on `DFS_n(J)` (at that
magnetic number) as `X = |i⟩⟨i′| + |i′⟩⟨i|`, `Y = i(|i⟩⟨i′| − |i′⟩⟨i|)`, `Z = |i⟩⟨i| − |i′⟩⟨i′|`.

**Formalization Note** Doubled labels shifted: `2J = jB + 1`; B-states lie in the eigenspace of
`(s^{n−1})²` with label `jB`, T-states with label `jB + 2`. `J < n/2 − 1` is `jB + 3 < n`. Any legal
magnetic number (the paper takes `m_J = J`). `i` and `i′` are orthogonal automatically. -/
theorem mix_any_su2 (n jB : ℕ) (hjtop : jB + 3 < n) (hind : SectorUniversal (n - 1)) (m2 : ℤ)
    (u u' : EuclideanSpace ℂ (Qubits n))
    (hu : u ∈ dfs n (jB + 1) m2 ⊓ casimirEigenspace n (n - 1) jB)
    (hu' : u' ∈ dfs n (jB + 1) m2 ⊓ casimirEigenspace n (n - 1) (jB + 2))
    (hnu : ‖u‖ = 1) (hnu' : ‖u'‖ = 1) :
    ∃ X ∈ sectorSet n (jB + 1), ∃ Y ∈ sectorSet n (jB + 1), ∃ Z ∈ sectorSet n (jB + 1),
      ∀ ψ ∈ dfs n (jB + 1) m2,
        Matrix.toEuclideanLin X ψ = inner ℂ u' ψ • u + inner ℂ u ψ • u' ∧
        Matrix.toEuclideanLin Y ψ = Complex.I • (inner ℂ u' ψ • u - inner ℂ u ψ • u') ∧
        Matrix.toEuclideanLin Z ψ = inner ℂ u ψ • u - inner ℂ u' ψ • u' := by sorry

end CollectiveDFS
