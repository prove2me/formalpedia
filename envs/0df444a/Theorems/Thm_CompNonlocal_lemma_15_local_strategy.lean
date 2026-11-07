-- Prove2me | Theorems.Thm_CompNonlocal_lemma_15_local_strategy
-- name    : CompNonlocal.lemma_15_local_strategy
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:49:22.412223+00:00
-- url     : https://prove2.me/theorems/79ffc9f0-1be7-4ffb-89f0-13c8e9868443
-- title:
--   Lemma 15, pp.41–42 — a local strategy from an approximate direction: $p\ge h_{5/12}-\frac\eta{16}-\frac{\sqrt{(1/2-\mathfrak a)\eta}}4-\varepsilon$
-- statement:
--   Let $\mathfrak a=\mathbb E[\langle w_{X,a},r(T)\rangle]$ (Definition 13). Suppose a polynomial-size estimator (possibly with advice) runs the §8.1 receiver $(a,\zeta)\leftarrow\mathrm{Rec}(x)$, computes on $(x,a,Q)$ and returns $n\in S^2$, and let $\eta=\mathbb E\|n-r(T)\|_2^2$. Then there are players $A',B'$ of size polynomial in $\kappa$ and $1/\varepsilon$ such that, for every $\varepsilon\in(0,1)$, their success probability in the certification game satisfies
--   $$p\ge h_{5/12}-\frac\eta{16}-\frac{\sqrt{(\frac12-\mathfrak a)\,\eta}}4-\varepsilon. \tag{32}$$
--   They use the estimator's advice and one fixed grid label, and no shared randomness.
--
--   Combined with Corollary 1, an accurate receiver-side estimator would give a separable strategy beating the soundness threshold.
--
--   Differences from the source:
--   - encoding: QPT algorithms and polynomial-size quantum circuit families with classical advice, no gate set fixed (§4, pp.17–18) → uniform (polynomial-time generated) or polynomial-size families of layered Clifford+T circuits with a fixed classical/quantum interface (ICirc); advice hard-wired; reason: Clifford+T is universal and the paper fixes no gate set (Reading 2); a non-uniform family subsumes polynomial-length advice
--   - encoding: Val outputs a score w ∈ [0, 1] (Def 8) or v ∈ [−1, 1] ∪ {⊥} (Def 9); acceptance is the event v₁ < 0, a discarded round rejected (Def 11) → Val outputs one accept bit, its first output bit; reason: only the acceptance event is used for k = 1 (Reading 3)
--   - encoding: real and vector outputs r̂ ∈ ℝ³, predictions in [−1, 1], directions n ∈ S² → fixed dyadic decodings decDyadic, decVec, decDir; predictions clipped to [−1, 1]; reason: the paper fixes no bit format; decodable values are dense (Reading 5)
--   - encoding: Alice's algorithm A(x, ω_A) acts on her qubit → hypothesis 1 ≤ (c.A κ).nq: the honest Alice circuit reads at least one quantum-input wire; reason: in the circuit model a circuit may ignore its quantum input; the paper's A(x, ω_A) and the §8.1 receiver run Alice's circuit on her qubit
--   - generalization: a certificate for a Werner state with uniform QPT honest players (the setting of Theorem 6) → any certificate whose honest A, B are polynomial-size; reason: the construction uses only the sizes of A, B; uniform families are polynomial-size
--   - encoding: running time polynomial in κ and 1/ε → size and width at most P(κ + ⌈1/ε⌉) for one polynomial P; reason: a univariate polynomial in κ + ⌈1/ε⌉ bounds every bivariate polynomial and conversely
--   - reading: 'no shared randomness … the shared separable state can be taken to be a fixed product state' (p.43) → the bound holds at every κ for every two-qubit density matrix τ; reason: the strategy ignores its shared state; the universal form implies the fixed-product-state form
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 15, pp.41–42, Eq. (32)

import Mathlib
import Definitions.Def_CompNonlocal_Certificate_acc
import Definitions.Def_CompNonlocal_Certificate_align
import Definitions.Def_CompNonlocal_Certificate_estimatorError
import Definitions.Def_CompNonlocal_PolySize
import Definitions.Def_CompNonlocal_werner
import Definitions.Def_QAlgorithms_Defs_Information

set_option autoImplicit false

namespace CompNonlocal

/-- **Lemma 15 (A local strategy from an approximate direction).** Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), pp.41–42: "Recall from Definition 13 that 𝔞 := E[⟨w_{X,a}, r(T)⟩].
Assume there exists a QPT algorithm in κ, possibly with classical advice, that runs (a, ζ) ←
ASP.Rec(x), followed by some computation on (x, a, Q), and returns n ∈ S². Let η := E[∥n − r(T)∥₂²].
There exists a pair of algorithms A′, B′ running in polynomial time in κ and 1/ε such that, for every
ε ∈ (0, 1), their success probability p in the certification game satisfies
p ≥ h_{5/12} − η/16 − √((1/2 − 𝔞)η)/4 − ε. (32) The algorithms use the classical advice of the
estimator together with one fixed grid label, and no shared randomness."

**Formalization Note** The certificate's honest Alice and Bob are polynomial-size and Alice reads her
qubit (the §8.1 receiver runs her circuit); no gap hypothesis is used. The estimator is a
polynomial-size family `Est` on `(x, a, Q)` (`a` the complete record), `η = c.estimatorError κ (Est κ)`.
"Polynomial time in κ and 1/ε" is: size and width at most `P(κ + ⌈1/ε⌉)` for one polynomial `P`.
"No shared randomness" is: the bound holds at every `κ` for every two-qubit density matrix `τ` given
to the players (the strategy does not use its state), in particular for a fixed product state. -/
theorem lemma_15_local_strategy (c : Certificate) (hA : PolySize c.A) (hB : PolySize c.B)
    (hnq : ∀ κ, 1 ≤ (c.A κ).nq) (Est : Family) (hEst : PolySize Est) :
    ∃ P : Polynomial ℕ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ A' B' : Family,
      (∀ κ, (A' κ).size ≤ P.eval (κ + ⌈1 / ε⌉₊) ∧ (A' κ).width ≤ P.eval (κ + ⌈1 / ε⌉₊)) ∧
      (∀ κ, (B' κ).size ≤ P.eval (κ + ⌈1 / ε⌉₊) ∧ (B' κ).width ≤ P.eval (κ + ⌈1 / ε⌉₊)) ∧
      ∀ (κ : ℕ) (τ : Matrix (Bool × Bool) (Bool × Bool) ℂ), QAlgorithms.IsDensityMatrix τ →
        c.acc κ c.A c.B (werner (5 / 12)) - c.estimatorError κ (Est κ) / 16 -
            Real.sqrt ((1 / 2 - c.align κ) * c.estimatorError κ (Est κ)) / 4 - ε ≤
          c.acc κ A' B' τ := by sorry

end CompNonlocal
