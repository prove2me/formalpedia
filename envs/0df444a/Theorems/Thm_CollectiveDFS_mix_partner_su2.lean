-- Prove2me | Theorems.Thm_CollectiveDFS_mix_partner_su2
-- name    : CollectiveDFS.mix_partner_su2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:09:58.840604+00:00
-- url     : https://prove2.me/theorems/27ce4d28-aae8-4958-878f-279d71bedab4
-- title:
--   (7.28)–(7.30), p.27 — $\mathfrak{su}(2)$ between a TB state and its BT partner on $\mathrm{DFS}_n(J)$ only
-- statement:
--   Assume exchange acts as $\mathfrak{su}$ independently on every $\mathrm{DFS}_{n-1}(J')$ (the induction hypothesis), and let $0<J<n/2-1$. Let $a$ be a unit vector of a TB path line of $\mathrm{DFS}_n(J)$ (last spins $(J,J-\tfrac12,J)$) and $a'$ a unit vector of the BT path line with the same $J_1,\dots,J_{n-2}$ (last spins $(J,J+\tfrac12,J)$), at a common magnetic number $m$. Then there are $X,Y,Z\in H^n_J$ that act on $\mathrm{DFS}_n(J)$ at $m$ as
--   $$X=|a\rangle\langle a'|+|a'\rangle\langle a|,\qquad Y=i\big(|a\rangle\langle a'|-|a'\rangle\langle a|\big),\qquad Z=|a\rangle\langle a|-|a'\rangle\langle a'|,$$
--   and as zero on the rest of that DFS.
--
--   This is Step 1 of the proof: an $\mathfrak{su}(2)$ that mixes a specific B-state with its T-partner and acts on no other DFS.
--
--   Differences from the source:
--   - reading: |a⟩, |b⟩ any two orthogonal BT-states; {|a′⟩, |b′⟩} a pair of orthogonal BT-states → a in a TB line, a′ in the BT line with the same first n − 2 spins; reason: (7.24)–(7.25) and (7.27) put a, b at +cos θ_J, which is TB; the text also calls a 'a specific B-state' and a′ 'its corresponding T-state'
--   - generalization: a′ with the phase of (7.27), so ⟨a|E|a′⟩ = sin θ_J → any unit a′ in the BT line; reason: the su(2) on span{a, a′} contains the three operators for every phase; the printed phase is a special case
--   - generalization: m_J fixed (m_J = J in the proof) → every legal magnetic number m; reason: exchange commutes with the S_α (fact (i), (7.13)); the statement at m = J is a special case
--   - reading: induction hypothesis: su(n_J) on each DFS_{n−1}(J) independently using only exchange operators and the identity Hamiltonian → SectorUniversal (n − 1): exchange alone, traceless elements of H^{n−1}_J; reason: Theorem 5, which the induction proves, is stated for exchange alone; su elements are traceless, so the identity Hamiltonian contributes nothing to them
--   - encoding: 0 < J < n/2 − 1 (with n > 4) → 2J = jB + 1 with jB + 3 < n; reason: avoids natural-number subtraction; n > 4 follows from jB + 3 < n and the parity of a path
--   - encoding: qubits 1, …, n; |0⟩, |1⟩ → 0-based wires Fin n; Bool basis with false = |0⟩; reason: Lean convention; same operators
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eqs. (7.27)–(7.30), p.27

import Mathlib
import Definitions.Def_CollectiveDFS_SectorUniversal
import Definitions.Def_CollectiveDFS_IsPath
import Definitions.Def_CollectiveDFS_pathSpace

open QAlgorithms

namespace CollectiveDFS

/-- Step 1 of the proof of Theorem 5, eqs. (7.28)–(7.30) (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, §VII.D.1, p.27, PDF p.27): "for
J < n/2 − 1 we can validly (using only exchange Hamiltonians) perform su(2) operations between
|a⟩, a specific B-state and |a′⟩, its corresponding T-state, on DFS_n(J) only". Assume exchange
acts as `su` independently on every `DFS_{n−1}` (the induction hypothesis). Let `0 < J < n/2 − 1`,
let `a` be a unit vector of a TB path line of `DFS_n(J)` (last spins `(J, J−½, J)`) and `a′` a
unit vector of the BT path line with the same `J_1, …, J_{n−2}` (last spins `(J, J+½, J)`), at a
common magnetic number. Then there are `X, Y, Z ∈ H^n_J` acting on `DFS_n(J)` (at that magnetic
number) as `X = |a⟩⟨a′| + |a′⟩⟨a|`, `Y = i(|a⟩⟨a′| − |a′⟩⟨a|)`, `Z = |a⟩⟨a| − |a′⟩⟨a′|`, and as
zero on the rest of it.

**Formalization Note** Doubled labels shifted to avoid subtraction: `2J = jB + 1`, so the TB path
`pB` has `(2J_{n−2}, 2J_{n−1}, 2J_n) = (jB+1, jB, jB+1)` and the BT path `pT` has
`(jB+1, jB+2, jB+1)`; `J > 0` is built in. `J < n/2 − 1` is `jB + 3 < n`; it implies the paper's
`n > 4` together with the parity of a path. The magnetic number is any legal one (the paper takes
`m_J = J`); the phase of `a′` is arbitrary. `|a⟩⟨a′| ψ` is `⟪a′, ψ⟫ • a`, the inner product
being conjugate-linear in its first argument. -/
theorem mix_partner_su2 (n jB : ℕ) (hjtop : jB + 3 < n) (hind : SectorUniversal (n - 1))
    (m2 : ℤ) (pB pT : Fin n → ℕ) (hpB : IsPath pB) (hpT : IsPath pT)
    (hpre : ∀ k : Fin n, (k : ℕ) < n - 2 → pB k = pT k)
    (hB3 : pB ⟨n - 3, by omega⟩ = jB + 1) (hB2 : pB ⟨n - 2, by omega⟩ = jB)
    (hB1 : pB ⟨n - 1, by omega⟩ = jB + 1)
    (hT2 : pT ⟨n - 2, by omega⟩ = jB + 2) (hT1 : pT ⟨n - 1, by omega⟩ = jB + 1)
    (a a' : EuclideanSpace ℂ (Qubits n)) (ha : a ∈ pathSpace pB m2) (ha' : a' ∈ pathSpace pT m2)
    (hna : ‖a‖ = 1) (hna' : ‖a'‖ = 1) :
    ∃ X ∈ sectorSet n (jB + 1), ∃ Y ∈ sectorSet n (jB + 1), ∃ Z ∈ sectorSet n (jB + 1),
      ∀ ψ ∈ dfs n (jB + 1) m2,
        Matrix.toEuclideanLin X ψ = inner ℂ a' ψ • a + inner ℂ a ψ • a' ∧
        Matrix.toEuclideanLin Y ψ = Complex.I • (inner ℂ a' ψ • a - inner ℂ a ψ • a') ∧
        Matrix.toEuclideanLin Z ψ = inner ℂ a ψ • a - inner ℂ a' ψ • a' := by sorry

end CollectiveDFS
