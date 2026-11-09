-- Prove2me | Theorems.Thm_CliffordCert_Optimal_certification_upper_bound
-- name    : CliffordCert.Optimal.certification_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:48:11.952832+00:00
-- url     : https://prove2.me/theorems/99f9d3c4-54f4-4681-a529-373eb440146c
-- title:
--   Theorem 3 — explicit certification upper bound
-- statement:
--   For every $1\le q\le n$, put $d=2^n$ and $r=2^q$. There exists a nonempty Clifford family depending only on $n,q$ such that for every known density matrix $\sigma$ and every $0<\varepsilon\le1$, the exact block spectral protocol of Eqs. (4)–(6) satisfies
--   $$L\le6d^2/r^2,\qquad s=\lceil128d/\varepsilon^2\rceil,\qquad m=Ls\le774d^3/(r^2\varepsilon^2).$$
--   The actual binary effect is positive and bounded by identity, its acceptance probability equals the independent Born block formula, and its encoder schedule is CPTP. It accepts the null with probability at least $2/3$ and rejects every alternative state $\rho$ with $\|\rho-\sigma\|_1\ge\varepsilon$ with probability at least $2/3$. It accepts exactly when $\widehat D<\varepsilon^2/(2rL)$ and rejects equality. The original input alone is Clifford-encoded and its last $n-q$ qubits discarded.
--
--   This is the explicit uniform upper bound, including the physical protocol rather than assumed moments or assumed success.
--
--   Differences from the source:
--   - encoding: n-qubit matrices and labelled tensor registers → matrices indexed by Fin n → Fin 2 and tensor configurations indexed by finite functions; reason: these are the computational bases, with the first q qubits retained and the last n−q discarded
--   - encoding: the protocol above with a fixed Theorem 2 family → existence of one physical Clifford family with all exact block-test conclusions; reason: the family is quantified before all references and accuracies and success is only a conclusion
--   - encoding: field-valued binary labels and Clifford matrices → published signed Pauli and individual Clifford definitions with Fin 2 label and bundled-unitary adapters; reason: binary residues 0 and 1 preserve the Eq. (18) phase and tensor order; the Clifford predicate requires every list member, with no random weights
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 6, Theorem 3; proof §E.2 p. 17 (PDF p. 18) (PDF p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_CliffordCert_Optimal_spectral_protocol
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq

theorem certification_upper_bound (n q : ℕ) (hq : 1 ≤ q) (hqn : q ≤ n) :
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
      ∀ ρ, IsState ρ → ε ≤ WildeQIT.traceNorm (ρ - σ) → blockAcceptance hqn C σ ρ ε ≤ 1 / 3 := by sorry
end CliffordCert.Optimal
