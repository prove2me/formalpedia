-- Prove2me | Theorems.Thm_FRouting_Supplement_theorem_7_10
-- name    : FRouting.Supplement.theorem_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T14:24:29.390223+00:00
-- url     : https://prove2.me/theorems/e8a08a8c-1839-4c4d-b691-d76ed5fbba99
-- title:
--   Theorem 7.10 — quantum fidelity estimation for non-explicit Pauli-sparse unitaries
-- statement:
--   Let $U$ and $V$ be unitaries on $q$ qubits given by quantum circuits with no input wires, both $(q,s)$-Pauli-sparse: at most $s$ of their Pauli coefficients $2^{-q}\operatorname{tr}(UP)$, $P\in\{I,X,Y,Z\}^{\otimes q}$, are nonzero. Let $L$ bound the length of the two circuit descriptions, let $A$ be a common set of output wires, and put
--   $$\rho=\operatorname{tr}_{\bar A}\bigl(U|0^q\rangle\langle0^q|U^\dagger\bigr),\qquad \sigma=\operatorname{tr}_{\bar A}\bigl(V|0^q\rangle\langle0^q|V^\dagger\bigr).$$
--
--   There are a classical machine $M$ and a constant $c$ such that, for all such $U,V$ and every $k\ge1$, $M$ on input the two descriptions, $s$ and $k$ (in unary) prints within $\tau=c\,(q+s+L+k+2)^c$ steps a qubit circuit of size and width at most $\tau$, and measuring its output qubits in the computational basis yields, with probability at least $2/3$, a string beginning with the description of a rational $\widetilde F$ with
--   $$\bigl|\widetilde F-F(\rho,\sigma)\bigr|\le 1/k,$$
--   where $F$ is the root fidelity. Thus $F(\rho,\sigma)$ is estimated to additive error $\delta$ by a bounded-error quantum algorithm in time $\mathrm{poly}(q,s,L,1/\delta)$.
--
--   This is the estimation step for non-explicit Pauli-sparse adversaries in §7.
--
--   Differences from the source:
--   - reading: "For every δ ∈ (0, 1), there is a bounded-error quantum algorithm" in time poly(q, s, L, 1/δ) → one algorithm for all inputs, given (desc U, desc V, s in unary, k in unary) with δ = 1/k; reason: the printed order lets the algorithm depend on q, s, L, δ; one algorithm taking them as input is the stronger reading and covers every δ ∈ (0,1) by k = ⌈1/δ⌉ ≤ 2/δ
--   - reading: bounded-error quantum algorithm (not defined in the paper) → a classical machine prints within the time bound a qubit circuit of size and width within the bound; measuring its kept qubits gives, with probability ≥ 2/3, a string beginning with the description of a rational within δ of F(ρ, σ); reason: the standard uniform-circuit model with success probability 2/3; intermediate measurements are deferred, the paper's convention
--   - reading: U, V given by quantum circuits of description length ≤ L → circuits of the base mission (gates X, Z, H, T, CNOT on qubits), L the total length of their descriptions encCircuit; reason: the paper fixes no gate set or description; the base mission's circuit model and description are used throughout
--   - encoding: Pauli strings P ∈ {I, X, Y, Z}^{⊗q} and coefficients 2^{-q} tr(UP) → the published labels (a,b) ↦ i^{ab}X^aZ^b and normalized coefficient tr(P†U)/2^q; reason: these label exactly I, X, Z, Y, every Pauli is Hermitian, and trace is cyclic, so the support is unchanged
--   - generalization: each circuit has description length at most L → the running time uses the actual sum |encCircuit U| + |encCircuit V|; reason: if each source description has length at most L then the sum is at most 2L, absorbed by the polynomial, while the actual-length bound also covers unequal descriptions
--   - encoding: poly(q, s, L, 1/δ) → c·(q + s + L + k + 2)^c for one constant c; reason: every polynomial with nonnegative arguments is bounded by such an expression and each such expression is a polynomial
--   - generalization: δ ∈ (0, 1) → also k = 1, i.e. δ = 1; reason: an extra input with an easy requirement; the instances δ ∈ (0,1) are unchanged
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 7.10, p.35 (Definition 7.1, p.31)

import Definitions.Def_FRouting_Supplement_PauliSparse
import Definitions.Def_FRouting_Supplement_measureProb
import Definitions.Def_FRouting_Supplement_encRat
import Definitions.Def_FRouting_StrMachine
import Definitions.Def_WildeQIT_fidelity

set_option autoImplicit false

namespace FRouting.Supplement

open WildeQIT QAlgorithms.Complexity

/-- **Theorem 7.10 — quantum fidelity estimation for non-explicit Pauli-sparse unitaries.** Renard,
*Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 7.10, p.35:
"Let U, V be non-explicit (q, s)-Pauli-sparse unitaries given by quantum circuits of description length
at most L, and let ρ := tr_Ā(U|0^q⟩⟨0^q|U†), σ := tr_Ā(V|0^q⟩⟨0^q|V†). For every δ ∈ (0, 1), there is a
bounded-error quantum algorithm that estimates F(ρ, σ) up to additive error δ in time poly(q, s, L, 1/δ)."

**Formalization Note** `U, V` are published qubit circuits with no input wires and `q` ancillas each, so
`U|0^q⟩` is the circuit applied to `|0^q⟩`; the same `a` kept wires form `A`, and `ρ, σ` are the output
states. Pauli sparsity (Definition 7.1) is that of the full `q`-qubit circuit unitary. The description
length is that of `encCircuit`. A bounded-error quantum algorithm is a classical machine `M` that prints,
within the time bound, a qubit circuit (of size and width within the bound) whose kept qubits are
measured in the computational basis; with probability at least `2/3` the outcome begins with the
encoding of a rational `F̃` with `|F̃ − F(ρ, σ)| ≤ δ`. One `M` for all inputs, given `s` and `k` in
unary, with `δ = 1/k`, so every `δ ∈ (0, 1)` is covered by `k = ⌈1/δ⌉`. `poly(·)` is
`c (q + s + L + k + 2)ᶜ`. `F` is the root fidelity. -/
theorem theorem_7_10 :
    ∃ (M : StrMachine) (c : ℕ), ∀ (q a s k : ℕ) (U V : Circuit 2 0 a),
      U.ancillas = q → V.ancillas = q → IsPauliSparse U.unitary s → IsPauliSparse V.unitary s →
      1 ≤ k →
      ∃ (m : ℕ) (C : Circuit 2 0 m),
        PrintsInTime M (encCircuit U ++ encCircuit V ++ encNat s ++ encNat k) (encCircuit C)
          (c * (q + s + ((encCircuit U).length + (encCircuit V).length) + k + 2) ^ c) ∧
        C.size ≤ c * (q + s + ((encCircuit U).length + (encCircuit V).length) + k + 2) ^ c ∧
        C.width ≤ c * (q + s + ((encCircuit U).length + (encCircuit V).length) + k + 2) ^ c ∧
        (2 / 3 : ℝ) ≤ measureProb C (fun out => ∃ r : ℚ, encRat r <+: out ∧
          |(r : ℝ) - rootFidelity U.outputState V.outputState| ≤ 1 / (k : ℝ)) := by sorry

end FRouting.Supplement
