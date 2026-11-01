-- Prove2me | Theorems.Thm_CollectiveDFS_exchange_last_two
-- name    : CollectiveDFS.exchange_last_two
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T16:05:59.927034+00:00
-- url     : https://prove2.me/theorems/c2f85569-9ef9-4f17-90a1-7305591ccda2
-- title:
--   (7.26), p.27 (corrected: $\theta_J$, not $\theta_{J+1}$) — exchange of the last two qubits on TT, BT, TB, BB
-- statement:
--   Let $n\ge 3$, $E=E_{n,n-1}$ the exchange of the last two qubits, and $\theta_J\in[0,\pi/2)$ with $\tan\theta_J=2\sqrt{J(J+1)}$, so $\cos\theta_J=1/(2J+1)$. Label a path state of $\mathrm{DFS}_n(J)$ by its last three spins $(J_{n-2},J_{n-1},J_n)$, as in (7.24)–(7.25): TT $=(J+1,J+\tfrac12,J)$, BT $=(J,J+\tfrac12,J)$, TB $=(J,J-\tfrac12,J)$, BB $=(J-1,J-\tfrac12,J)$. At every legal magnetic number $m$:
--   1. $E$ fixes every vector of a TT line and of a BB line;
--   2. if $J=0$, $E$ acts as $-1$ on a BT line;
--   3. if $J>0$, for a BT path and a TB path with the same $J_1,\dots,J_{n-2}$, $E$ maps the sum of their two lines into itself, and for unit vectors $\psi$ (BT) and $\varphi$ (TB)
--   $$\langle\psi,E\psi\rangle=-\cos\theta_J,\qquad\langle\varphi,E\varphi\rangle=\cos\theta_J,\qquad|\langle\varphi,E\psi\rangle|=\sin\theta_J.$$
--
--   Exchange of the last two qubits thus mixes the BT and TB states entering a DFS and leaves the BB and TT states invariant; this is the step of the proof where exchange acts between B- and T-states.
--
--   Differences from the source:
--   - correction: (7.26): middle block −cos θ_{J+1}, sin θ_{J+1}, cos θ_{J+1} → θ_J; reason: n = 3, J = ½: (7.18) gives E₂₃ = ±½ on the two DFS_3(1/2) states, and cos θ_{1/2} = ½ while cos θ_{3/2} = ¼; θ_J also agrees with (7.27)
--   - reading: tan θ_J = 2√(J(J+1)) → θ_J = arctan(2√(J(J+1))) ∈ [0, π/2); reason: the branch for which (7.26) agrees with (7.18) and (7.27)
--   - encoding: off-diagonal entry sin θ_J in the basis (B8) → |⟨φ, Eψ⟩| = sin θ_J for any unit vectors of the two lines; reason: the lines carry no phase convention; with the (B5) phases the entry is +sin θ_J
--   - reading: the 4×4 matrix, assuming the existence of the given states → one clause per existing block: TT, BB, the BT–TB pair for J > 0, and the BT line alone for J = 0; reason: the paper's proviso; at J = 0 only BT and TT exist
--   - generalization: m_J fixed (m_J = J in the proof) → every legal magnetic number m; reason: exchange commutes with the S_α (fact (i), (7.13)); the statement at m = J is a special case
--   - encoding: qubits 1, …, n; |0⟩, |1⟩ → 0-based wires Fin n; Bool basis with false = |0⟩; reason: Lean convention; same operators
--   - encoding: half-integer labels J, m → doubled labels j2 = 2J : ℕ, m2 = 2m : ℤ; reason: exact half-integers; same instances
-- source:
--   Kempe, Bacon, Lidar & Whaley, Theory of Decoherence-Free Fault-Tolerant Universal Quantum Computation, arXiv:quant-ph/0004064v2, eqs. (7.24)–(7.26), pp.26–27

import Mathlib
import Definitions.Def_CollectiveDFS_exchange
import Definitions.Def_CollectiveDFS_LegalM
import Definitions.Def_CollectiveDFS_IsPath
import Definitions.Def_CollectiveDFS_pathSpace

open QAlgorithms

namespace CollectiveDFS

/-- Eq. (7.26) with `θ_J` (Kempe, Bacon, Lidar & Whaley, arXiv:quant-ph/0004064v2, eqs. (7.24)–(7.26), pp.26–27, PDF pp.26–27): the action of the
exchange `E = E_{n,n−1}` of the last two qubits on the path states of `DFS_n(J)`, `n ≥ 3`, at any
legal `m`. Let `tan θ_J = 2√(J(J+1))`, `θ_J ∈ [0, π/2)`. Labelling the last three spins
`(J_{n−2}, J_{n−1}, J_n)` as in (7.24)–(7.25), TT = `(J+1, J+½, J)`, BT = `(J, J+½, J)`,
TB = `(J, J−½, J)`, BB = `(J−1, J−½, J)`:
(1) `E` fixes every vector of a TT line and of a BB line;
(2) at `J = 0`, `E` is `−1` on a BT line;
(3) for `J > 0` and a BT path and a TB path with the same `J_1, …, J_{n−2}`, `E` maps the sum of
their two lines into itself, and for unit vectors `ψ` (BT) and `φ` (TB):
`⟨ψ, Eψ⟩ = −cos θ_J`, `⟨φ, Eφ⟩ = cos θ_J`, `|⟨φ, Eψ⟩| = sin θ_J`.

**Formalization Note** Doubled labels, 0-based positions: `p (n−3), p (n−2), p (n−1)` are
`2J_{n−2}, 2J_{n−1}, 2J_n`; `E = exchange (n−2) (n−1)` on 0-based wires. The off-diagonal entry
is stated in modulus because the path lines carry no phase convention; with the (B5) phases it
is `+sin θ_J`. Corrected: the printed (7.26) has `θ_{J+1}`; at `n = 3`, `J = ½`, (7.18) gives
`cos = ½ = cos θ_{1/2}`, while `cos θ_{3/2} = ¼`. -/
theorem exchange_last_two (n : ℕ) (hn : 3 ≤ n) (j2 : ℕ) (m2 : ℤ) (hm : LegalM j2 m2) :
    (∀ p : Fin n → ℕ, IsPath p → p ⟨n - 3, by omega⟩ = j2 + 2 → p ⟨n - 2, by omega⟩ = j2 + 1 →
      p ⟨n - 1, by omega⟩ = j2 → ∀ ψ ∈ pathSpace p m2,
        Matrix.toEuclideanLin (exchange (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) ψ = ψ) ∧
    (∀ p : Fin n → ℕ, IsPath p → p ⟨n - 3, by omega⟩ + 2 = j2 → p ⟨n - 2, by omega⟩ + 1 = j2 →
      p ⟨n - 1, by omega⟩ = j2 → ∀ ψ ∈ pathSpace p m2,
        Matrix.toEuclideanLin (exchange (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) ψ = ψ) ∧
    (j2 = 0 → ∀ p : Fin n → ℕ, IsPath p → p ⟨n - 3, by omega⟩ = 0 → p ⟨n - 2, by omega⟩ = 1 →
      p ⟨n - 1, by omega⟩ = 0 → ∀ ψ ∈ pathSpace p m2,
        Matrix.toEuclideanLin (exchange (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) ψ = -ψ) ∧
    (1 ≤ j2 → ∀ p q : Fin n → ℕ, IsPath p → IsPath q →
      (∀ k : Fin n, (k : ℕ) < n - 2 → p k = q k) →
      p ⟨n - 3, by omega⟩ = j2 → p ⟨n - 2, by omega⟩ = j2 + 1 → p ⟨n - 1, by omega⟩ = j2 →
      q ⟨n - 2, by omega⟩ + 1 = j2 → q ⟨n - 1, by omega⟩ = j2 →
      (∀ ψ ∈ pathSpace p m2 ⊔ pathSpace q m2,
        Matrix.toEuclideanLin (exchange (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) ψ ∈
          pathSpace p m2 ⊔ pathSpace q m2) ∧
      ∀ ψ ∈ pathSpace p m2, ∀ φ ∈ pathSpace q m2, ‖ψ‖ = 1 → ‖φ‖ = 1 →
        inner ℂ ψ (Matrix.toEuclideanLin
            (exchange (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) ψ) =
          ((-Real.cos (Real.arctan (2 * Real.sqrt ((j2 : ℝ) / 2 * ((j2 : ℝ) / 2 + 1))))
            : ℝ) : ℂ) ∧
        inner ℂ φ (Matrix.toEuclideanLin
            (exchange (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) φ) =
          ((Real.cos (Real.arctan (2 * Real.sqrt ((j2 : ℝ) / 2 * ((j2 : ℝ) / 2 + 1)))) : ℝ) : ℂ) ∧
        ‖inner ℂ φ (Matrix.toEuclideanLin
            (exchange (⟨n - 2, by omega⟩ : Fin n) ⟨n - 1, by omega⟩) ψ)‖ =
          Real.sin (Real.arctan (2 * Real.sqrt ((j2 : ℝ) / 2 * ((j2 : ℝ) / 2 + 1))))) := by sorry

end CollectiveDFS
