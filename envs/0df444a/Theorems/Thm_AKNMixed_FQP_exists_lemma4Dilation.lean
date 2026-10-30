-- Prove2me | Theorems.Thm_AKNMixed_FQP_exists_lemma4Dilation
-- name    : AKNMixed.FQP.exists_lemma4Dilation
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:29.285099+00:00
-- url     : https://prove2.me/theorems/55be459a-bb38-4aa8-a597-2df0931867f3
-- title:
--   Lemma 4 — every gate has a unitary dilation on $n+m+\max(n,m)$ qubits (corrected: the printed $2n+m$ is too small when $m>n$)
-- statement:
--   Let $g$ be a quantum gate of order $(n,m)$. There is a unitary $U_g$ on $n+m+\max(n,m)$ qubits (that is, $2n+m$ qubits when $m\le n$) such that for every $n$-qubit $\rho$
--
--   $$g\circ\rho=\Bigl(U_g\circ\bigl(\rho\otimes|0\cdots0\rangle\langle0\cdots0|\bigr)\Bigr)\Big|_A ,$$
--
--   where $\rho$ occupies the first $n$ qubits, the $m+\max(n,m)$ blank qubits (the paper's $n+m$ when $m\le n$) the remaining ones, and $A$ is the set of the first $m$ qubits.
--
--   General gates can therefore be replaced by unitary gates on blank ancillas followed by discarding; the gate set of Theorem 2 is built from these $U_g$.
--
--   Differences from the source:
--   - correction: U_g on 2n + m qubits, ρ ⊗ |0^{n+m}⟩⟨0^{n+m}| → U_g on n + m + max(n, m) qubits, ρ ⊗ |0…0⟩⟨0…0| with m + max(n, m) blanks (identical to the printed form when m ≤ n); reason: the printed lemma is false for m > n: g(ρ) = Tr(ρ)·I/4 of order (1, 2) is linear, trace preserving and completely positive with Choi rank 8, but ρ ↦ (U(ρ ⊗ |000⟩⟨000|)U†)|_A for a unitary U on 4 qubits, A the first 2, traces out 2 qubits and so has at most 4 Kraus operators; the proof on p. 9 itself uses V : N → M ⊗ F with F = C^{2^{n+m}}, i.e. n + 2m output qubits
--   - encoding: for any ρ (a density matrix on n qubits) → for every matrix ρ on n qubits; reason: g is linear and density matrices span all matrices, so the two are equivalent
-- source:
--   Aharonov, Kitaev, Nisan, Quantum Circuits with Mixed States, arXiv:quant-ph/9806029v1, Lemma 4, p. 9

import Mathlib
import Definitions.Def_AKNMixed_FQP_QGate
import Definitions.Def_AKNMixed_FQP_IsLemma4Dilation

namespace AKNMixed.FQP

/-- **Lemma 4 (corrected register size): every gate has a unitary dilation on
`n + m + max n m` qubits (the printed `2n + m` when `m ≤ n`).**

Aharonov, Kitaev, Nisan, *Quantum Circuits with Mixed States*, arXiv:quant-ph/9806029v1,
Lemma 4, p. 9: "Let g be a quantum gate of order (n, m). There exists a unitary quantum gate U_g
on 2n + m qubits which satisfies: For any ρ, g ∘ ρ = (U_g ∘ (ρ ⊗ |0^{n+m}⟩⟨0^{n+m}|))|_A, where A
is the set of the first m qubits."

For every quantum gate `g` (linear, trace preserving, completely positive) of order `(n, m)`
there is a unitary `U` on `n + m + max n m` qubits such that, for every `n`-qubit `ρ`,
`g ∘ ρ = (U (ρ ⊗ |0…0⟩⟨0…0|) U†)|_A`, with `m + max n m` blanks and `A` the first `m` qubits
(`IsLemma4Dilation g U`).

**Formalization Note.** Correction: for `m ≤ n` the register is the printed `2n + m` qubits with
`n + m` blanks. For `m > n` the printed size is false: `ρ ↦ Tr(ρ) · I/4` of order `(1, 2)` has
Choi rank `8`, but a unitary on `4` qubits with `2` wires traced out yields at most `4` Kraus
operators. `n + m + max n m` qubits is what the proof on p. 9 (`V : N → M ⊗ F`,
`F = ℂ^{2^{n+m}}`) needs. `ρ` occupies the first `n` wires and the blanks the remaining ones; the
identity holds for every matrix `ρ`. -/
theorem exists_lemma4Dilation (g : QGate) (hg : g.IsQuantum) :
    ∃ U, IsLemma4Dilation g U := by sorry

end AKNMixed.FQP
