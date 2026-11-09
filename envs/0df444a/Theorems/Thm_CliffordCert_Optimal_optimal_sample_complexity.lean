-- Prove2me | Theorems.Thm_CliffordCert_Optimal_optimal_sample_complexity
-- name    : CliffordCert.Optimal.optimal_sample_complexity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:49:03.932616+00:00
-- url     : https://prove2.me/theorems/e6adadf5-c777-408d-8c9c-b26295aa411e
-- title:
--   Corollary 1 — optimal sample complexity with fixed Clifford encoders
-- statement:
--   There exist absolute constants $c>0$ and $0<\varepsilon_0\le1$ such that for all $1\le q\le n$, with $d=2^n$ and $r=2^q$, every uniform feasible budget $m$ for $0<\varepsilon\le\varepsilon_0$ satisfies
--   $$m\ge c\,\frac{d^3}{r^2\varepsilon^2}.$$
--   For each $n,q$ there is one nonempty fixed family of input-only Clifford compressions, depending only on these dimensions, such that for every known reference state $\sigma$ and every $0<\varepsilon\le1$, the exact spectral protocol of Eqs. (4)–(6) satisfies
--   $$L\le6d^2/r^2,\qquad m=L\lceil128d/\varepsilon^2\rceil\le774\,\frac{d^3}{r^2\varepsilon^2}.$$
--   It is a valid protocol in Eq. (15), with acceptance probability at least $2/3$ at $\rho=\sigma$ and at most $1/3$ for every density matrix separated from $\sigma$ by full trace norm at least $\varepsilon$. The family precedes the reference, accuracy and alternative in the quantifiers. The lower bound is worst case over references and covers arbitrary CPTP encoders, including averaged independent private coins.
--
--   Together these clauses give the full Θ claim and its all-accuracy fixed-Clifford upper bound. No minimization or possibly empty real infimum is used to encode optimality.
--
--   Differences from the source:
--   - encoding: worst-case private-coin sample complexity Ω(d³/(r²ε²)) for sufficiently small absolute ε₀ → positive absolute constants quantified before n, q and ε and a lower bound for every uniform feasible integer budget; reason: this expands Ω without adding a numeric constant or incorrectly requiring every reference to be hard
--   - encoding: n-qubit matrices and labelled tensor registers → matrices indexed by Fin n → Fin 2 and tensor configurations indexed by finite functions; reason: these are the computational bases, with the first q qubits retained and the last n−q discarded
--   - encoding: the asymptotic Clifford upper bound of Corollary 1 → the explicit 6 settings and 774 copies constants from Theorem 3 and its proof; reason: these source constants instantiate the corollary without dropping its all-accuracy range
--   - encoding: field-valued binary labels and Clifford matrices → published signed Pauli and individual Clifford definitions with Fin 2 label and bundled-unitary adapters; reason: binary residues 0 and 1 preserve the Eq. (18) phase and tensor order; the Clifford predicate requires every list member, with no random weights
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 6, Corollary 1; Theorem 3 and §E.2 p. 17 (PDF p. 18) (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_spectral_protocol
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem optimal_sample_complexity :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      (∀ (n q : ℕ), 1 ≤ q → q ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        ∀ m : ℕ, FeasibleBudget (Bits n) (Bits q) ε m →
          c * (2 : ℝ)^(3*n) / ((2 : ℝ)^(2*q) * ε^2) ≤ (m : ℝ)) ∧
      (∀ (n q : ℕ) (hq : 1 ≤ q) (hqn : q ≤ n),
        ∃ C : EncoderFamily n q, 
        0 < C.length ∧ (C.length : ℝ) ≤ 6 * (2 : ℝ)^(2*n) / (2 : ℝ)^(2*q) ∧
        ∀ (σ : Mat (Bits n)) (ε : ℝ), IsState σ → 0 < ε → ε ≤ 1 →
          2 ≤ blockSize n ε ∧
          ((C.length * blockSize n ε : ℕ) : ℝ) ≤ 774 * (2 : ℝ)^(3*n) / ((2 : ℝ)^(2*q) * ε^2) ∧
          (∀ j, WildeQIT.EntBreaking.IsQuantumChannel (blockSchedule hqn C ε j)) ∧
          IsEffect (blockEffect hqn C σ ε) ∧
          (∀ ρ, IsState ρ → born (tensorStates (fun j => blockSchedule hqn C ε j ρ))
            (blockEffect hqn C σ ε) = blockAcceptance hqn C σ ρ ε) ∧
          (2 / 3 : ℝ) ≤ blockAcceptance hqn C σ σ ε ∧
          ∀ ρ, IsState ρ → ε ≤ WildeQIT.traceNorm (ρ - σ) → blockAcceptance hqn C σ ρ ε ≤ 1 / 3) := by sorry
end CliffordCert.Optimal
