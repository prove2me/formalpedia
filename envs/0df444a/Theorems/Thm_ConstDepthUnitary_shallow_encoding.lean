-- Prove2me | Theorems.Thm_ConstDepthUnitary_shallow_encoding
-- name    : ConstDepthUnitary.shallow_encoding
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:46:33.25139+00:00
-- url     : https://prove2.me/theorems/9d8224a7-5902-4823-9662-5b6644f26a00
-- title:
--   §6.1 — the encoding isometry in constant depth
-- statement:
--   There are universal constants $d_0,C,c$ such that for all $n$ and $k\ge1$, with $N=2^n$ and $K=2^k$, there is a circuit $D$ with fan-out of depth at most $d_0$ on an $n$-qubit input register, $N$ registers $V_0,\dots,V_{N-1}$ of $k$ qubits each and $m$ ancillas, of width $n+Nk+m\le Cg(\log_2(g+2))^c$ with $g=NK$, such that for every $x$
--   $$D|x\rangle|0\rangle_V|0\rangle=|0^n\rangle\bigl(\hat E|x\rangle\bigr)_V|0\rangle.$$
--
--   The input is erased and only the encoded state remains, in constant depth.
--
--   Differences from the source:
--   - reading: width Õ(N log(N/ϵ)), with K = Θ(log(N/ϵ)) → width Õ(N K) for every k ≥ 1; reason: the bound in K gives the printed form at the printed choice of K; Õ as for Lemma 6.5
--   - encoding: the state across the V registers, with the X and B registers reset (Algorithms 2–3) → an amplitude identity on all wires: input register and ancillas at 0, big-endian V registers; reason: the same statement
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §6.1, Algorithms 2–3, p.38

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_EHat
import Definitions.Def_ConstDepthUnitary_decodeReg

namespace ConstDepthUnitary

/-- §6.1, Algorithms 2–3: the encoding isometry `Ê` in constant depth with fan-out and width `Õ(N K)`. With `N = 2^n`,
`K = 2^k`, the circuit maps `|x⟩ |0⟩ |0⟩ ↦ |0ⁿ⟩ (Ê |x⟩) |0⟩` for every `x`, on the input register, the `N` registers `V_j` of `k`
qubits each, and ancillas.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §6.1, Algorithms 2–3, p.38 (unnumbered claim).

**Formalization Note** The registers are big-endian (`decodeReg`, `QAlgorithms.bitsEquivFin`). The width is stated in `K`; with
`K = Θ(log(N/ε))` it is the printed `Õ(N log(N/ε))`. `k ≥ 1` keeps `K` even, so that `|ĥ₁⟩` is defined (`Z₁ > 0`). -/
theorem shallow_encoding :
    ∃ (d₀ : ℕ) (C : ℝ) (c : ℕ), ∀ n k : ℕ, 1 ≤ k →
      ∃ (m : ℕ) (D : Circuit (Fin n ⊕ (Fin (2 ^ n) × Fin k) ⊕ Fin m)),
        ((n + 2 ^ n * k + m : ℕ) : ℝ) ≤
          C * ((2 : ℝ) ^ n * 2 ^ k) * Real.logb 2 ((2 : ℝ) ^ n * 2 ^ k + 2) ^ c ∧
        D.depth ≤ d₀ ∧
        ∀ (x : Fin n → Bool) (y : Fin n ⊕ (Fin (2 ^ n) × Fin k) ⊕ Fin m → Bool),
          D.matrix.mulVec (Pi.single (Sum.elim x fun _ => false) 1) y =
            if (∀ i, y (Sum.inl i) = false) ∧ ∀ a, y (Sum.inr (Sum.inr a)) = false then
              EHat (2 ^ n) (2 ^ k) (decodeReg (2 ^ n) k fun p => y (Sum.inr (Sum.inl p)))
                (QAlgorithms.bitsEquivFin n x)
            else 0 := by sorry

end ConstDepthUnitary
