-- Prove2me | Theorems.Thm_EntangledPIR_claim_C_3
-- name    : EntangledPIR.claim_C_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:21.382906+00:00
-- url     : https://prove2.me/theorems/9b800795-f14b-4bdc-9668-89e94199b989
-- title:
--   Claim C.3 — the gate count of $U_g$
-- statement:
--   For every $g:\{0,1\}^d\to\{0,1\}^m$, the unitary $U_g$ can be implemented with $O(dm4^d)$ Pauli X, CNOT and Toffoli gates and $d-1$ ancilla qubits that are returned to zero, and so can $(U_g)_{\mathsf B}$ and the inverses of both unitaries.
--
--   This count dominates the resources of the honest servers, and is the reason they grow exponentially with $d$.
--
--   Differences from the source:
--   - encoding: finite-dimensional registers and tensor products → finite basis types, `Matrix` on them and `⊗ₖ`; reason: Lean convention; a register is its computational basis, same operators
--   - encoding: $\{0,1\}^d$ and $\oplus$ → `Fin d → Bool` and coordinatewise `xor`; reason: Lean convention; same strings
--   - encoding: $O(dm4^d)$ → one natural number $C$ before $d,m,g$; reason: the meaning of a uniform $O(\cdot)$
--   - encoding: "implemented" by these gates → a list of reversible gates maps each basis state with ancillas zero to its image under $U_g$ with ancillas zero; reason: a list of reversible gates permutes basis states, so this is equality of unitaries on that subspace
--   - encoding: $(U_g)_{\mathsf B}$ and the inverses → one list on the shared qubit labels, and the conjunct $U_gs\mapsto s$; reason: the paper identifies the labels of A and B (p.21) and $U_g$ is its own inverse (p.57)
-- source:
--   Mantri, Private Information Retrieval from Two Entangled Servers, manuscript (Nov. 2026; sha256 5cfce27c…51384), Claim C.3, p.57

import Definitions.Def_EntangledPIR_ElemOp

namespace EntangledPIR

/-- **Claim C.3**, Mantri, manuscript (Nov. 2026), p.57. For every `g : {0,1}^d → {0,1}^m`, the unitary `U_g` can be
implemented with `O(d m 4^d)` Pauli X, CNOT and Toffoli gates and `d − 1` ancilla qubits that are returned to zero,
and so can `(U_g)_B` and the inverses of both unitaries.

**Formalization Note.** `C` is absolute: it comes before `d`, `m`, `g`. A list of reversible gates is a permutation of
basis states, so it implements a unitary if it maps each basis state as that permutation does, with the ancillas zero
before and after. The list here maps `s ↦ U_g s`. `(U_g)_B` is the same matrix on the same labels (p.19, p.21). The
second conjunct, `U_g s ↦ s`, is the inverse (`U_g` is its own inverse, p.57). -/
theorem claim_C_3 : ∃ C : ℕ, ∀ (d m : ℕ), 1 ≤ d → ∀ g : Bits d → Bits m,
    ∃ gs : List (RevGate (CopyQubit d m ⊕ Fin (d - 1))),
      gs.length ≤ C * d * m * 4 ^ d ∧
      (∀ s : CopyReg d m,
        runGates gs (Sum.elim (qubitsOf s) (fun _ => false)) =
          Sum.elim (qubitsOf (UgFun g s)) (fun _ => false)) ∧
      (∀ s : CopyReg d m,
        runGates gs (Sum.elim (qubitsOf (UgFun g s)) (fun _ => false)) =
          Sum.elim (qubitsOf s) (fun _ => false)) := by sorry

end EntangledPIR
