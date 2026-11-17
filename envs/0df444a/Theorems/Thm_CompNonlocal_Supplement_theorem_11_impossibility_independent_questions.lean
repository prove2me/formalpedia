-- Prove2me | Theorems.Thm_CompNonlocal_Supplement_theorem_11_impossibility_independent_questions
-- name    : CompNonlocal.Supplement.theorem_11_impossibility_independent_questions
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:16:05.86721+00:00
-- url     : https://prove2.me/theorems/005e1bca-9802-4795-b716-66d0305b6ec3
-- title:
--   Theorem 11 — no public-verification certificate with independent questions for $\omega^*$; restricted UCN is false
-- statement:
--   In the model of Definition 9, with soundness as in Definition 10:
--
--   1. the state $\omega^*$ (the entangled state $\tilde\omega_{2/5}$ of Lemma 8 with pure local ancillas) is entangled and has **no** certificate with public verification, independent questions $X,Y$ and an inverse-polynomial gap, even with polynomially many independent repetitions;
--   2. consequently, UCN cannot hold under these restrictions: it is false that every entangled state has such a certificate.
--
--   Differences from the source:
--   - generalization: ω* with fixed constant-size pure local ancillas adjoined → omegaStar m_A m_B for every m_A, m_B ≥ 4 (2⁴ ≥ 12 labels λ); reason: the paper fixes one constant-size choice large enough for the label λ ∈ [12]; the statement for every such choice includes it
--   - encoding: ω* on C³ ⊗ C² (plus ancillas) → Alice's qutrit embedded in two qubits, |0⟩, |1⟩, |2⟩ ↦ |00⟩, |01⟩, |10⟩; all registers are qubit registers; reason: the computational model is qubit circuits; the embedded state has the same LHS model and the same separable comparison states
--   - generalization: UCN cannot hold under these restrictions (all finite-dimensional spaces) → ¬ RestrictedUCN, with RestrictedUCN quantified over qubit registers; reason: a counterexample on a qubit register is a counterexample among all finite-dimensional spaces, so the Lean statement implies the paper's
--   - reading: fixed constant-size pure local ancillas (pure state not named) → every ancilla qubit in |0⟩; reason: the paper does not name the pure state; any fixed pure product ancilla is local-unitarily equivalent to |0…0⟩, the circuit model's ancilla state
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Theorem 11, p.69

import Mathlib
import Definitions.Def_CompNonlocal_Supplement_omegaStar
import Definitions.Def_CompNonlocal_Supplement_RestrictedUCN

set_option autoImplicit false

namespace CompNonlocal.Supplement

/-- Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Theorem 11, p.69: "Theorem 11 (Impossibility with independent questions). In the model of
Definition 9, with soundness as in Definition 10, the entangled state ω∗ from Section 11 has no
public-verification certificate with independent questions X, Y and an inverse-polynomial gap, even
with polynomially many independent repetitions. Consequently, UCN cannot hold under these
restrictions."

1. For all ancilla sizes `m_A, m_B ≥ 4` (`2⁴ ≥ 12`, enough for the label `λ ∈ [12]` of p.63), the
   state `ω∗ = omegaStar m_A m_B` is entangled, and no game with public verification
   (`Game.IsPublic`) and independent questions (`Game.IndepQuestions`) is a certificate for it
   (`IsCertificateK`: any polynomial number of independent rounds, completeness `c`, soundness `s` as in
   Definition 10, gap `c − s > 1/poly`).
2. Consequently `RestrictedUCN` (every entangled state has such a certificate) is false.

**Formalization Note** The paper adjoins one fixed choice of constant-size ancillas; the statement
holds for every choice with at least four ancilla qubits on each side. -/
theorem theorem_11_impossibility_independent_questions :
    (∀ mA mB : ℕ, 4 ≤ mA → 4 ≤ mB →
      UnitalMIP.IsEntangled (omegaStar mA mB) ∧
        ¬ ∃ (G : Game) (cc s : ℕ → ℝ),
          G.IsPublic ∧ G.IndepQuestions ∧ IsCertificateK G (omegaStar mA mB) cc s) ∧
      ¬ RestrictedUCN := by sorry

end CompNonlocal.Supplement
