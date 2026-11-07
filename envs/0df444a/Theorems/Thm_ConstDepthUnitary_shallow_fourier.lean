-- Prove2me | Theorems.Thm_ConstDepthUnitary_shallow_fourier
-- name    : ConstDepthUnitary.shallow_fourier
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:48:15.354947+00:00
-- url     : https://prove2.me/theorems/28e70728-7070-4cb3-ad0f-15380ea51c5f
-- title:
--   §6.3 — the discrete Fourier transform in constant depth
-- statement:
--   There are universal constants $d_0$ and $C$ such that for all $N$ and $k\ge1$, with $K=2^k$, the transform $\hat F$ on $N$ registers of $k$ qubits each has a clean exact circuit with fan-out, of depth at most $d_0$ and width
--   $$Nk+m\le C\,NK^4.$$
--   All auxiliary registers return to zero and there is no approximation error.
--
--   Differences from the source:
--   - encoding: constants hidden in O(·) → an existential constant quantified before all data; reason: the paper's constants are universal
--   - encoding: registers holding the integers v_j ∈ [K], bit order unspecified → each register V_j = {j} × Fin k read big-endian (decodeReg, QAlgorithms.bitsEquivFin), the operator transported along this bijection; reason: a fixed bit order of the registers is a Lean convention and changes no instance
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §6.3, Algorithms 5–6, p.43

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_CleanlyImplements
import Definitions.Def_ConstDepthUnitary_FHat
import Definitions.Def_ConstDepthUnitary_decodeReg

namespace ConstDepthUnitary

/-- §6.3, Algorithms 5–6: the discrete Fourier transform `F̂` exactly, in constant depth with fan-out and width `O(N K⁴)`,
`K = 2^k`, on `N` registers of `k` qubits each, with all auxiliary registers returned to zero.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §6.3, Algorithms 5–6, p.43 (unnumbered claim). -/
theorem shallow_fourier :
    ∃ (d₀ : ℕ) (C : ℝ), ∀ N k : ℕ, 1 ≤ k →
      ∃ (m : ℕ) (D : Circuit ((Fin N × Fin k) ⊕ Fin m)),
        ((N * k + m : ℕ) : ℝ) ≤ C * (N : ℝ) * ((2 : ℝ) ^ k) ^ 4 ∧
        D.depth ≤ d₀ ∧
        CleanlyImplements D ((FHat N (2 ^ k)).submatrix (decodeReg N k) (decodeReg N k)) := by sorry

end ConstDepthUnitary
