-- Prove2me | Theorems.Thm_ConstDepthUnitary_shallow_phase
-- name    : ConstDepthUnitary.shallow_phase
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:48:31.025343+00:00
-- url     : https://prove2.me/theorems/eff51d01-eba3-43c6-ba8c-0ba4c390054a
-- title:
--   §6.2 — the quadratic phase in constant depth
-- statement:
--   There are universal constants $d_0$ and $C$ such that for all $N$, $k\ge1$ and every real symmetric $S$, with $K=2^k$, the phase $\hat Q_S$ on $N$ registers of $k$ qubits each has a clean exact circuit with fan-out of depth at most $d_0$ and space
--   $$Nk+m\le C\,N^2K^2k\log_2(k+2).$$
--
--   Differences from the source:
--   - generalization: S a traceless real symmetric unitary (the setting of Section 5) → any real symmetric S; reason: Algorithm 4 uses only that S is real symmetric; it specializes to the printed case
--   - reading: space O(N² log(N/ϵ)² log log(N/ϵ) log log log(N/ϵ)) → the same bound in k as in Step 2, O(N²K²k log k), with log₂(k + 2); reason: the displayed iterated logarithm is undefined at small arguments; at K = Θ(log(N/ϵ)) the two agree
--   - encoding: constants hidden in O(·) → an existential constant quantified before all data; reason: the paper's constants are universal
--   - encoding: registers holding the integers v_j ∈ [K], bit order unspecified → each register V_j = {j} × Fin k read big-endian (decodeReg, QAlgorithms.bitsEquivFin), the operator transported along this bijection; reason: a fixed bit order of the registers is a Lean convention and changes no instance
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §6.2, Algorithm 4, p.39

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_CleanlyImplements
import Definitions.Def_ConstDepthUnitary_QHat
import Definitions.Def_ConstDepthUnitary_decodeReg

namespace ConstDepthUnitary

/-- §6.2, Algorithm 4: the diagonal phase `Q̂_S` exactly, in constant depth with fan-out, on `N` registers of `k` qubits each,
with space `O(N² K² k log k)`, `K = 2^k`, for every real symmetric `S`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), §6.2, Algorithm 4, p.39 (unnumbered claim; the bound in `k` is Step 2's own "O(N²K²k log k)").

**Formalization Note** `log₂(k + 2)` keeps the bound positive at `k` small; the printed `log log log(N/ε)` is undefined at small
arguments. The space counts the `N k` qubits of the registers and the ancillas. The algorithm uses only that `S` is real symmetric. -/
theorem shallow_phase :
    ∃ (d₀ : ℕ) (C : ℝ), ∀ (N k : ℕ), 1 ≤ k → ∀ S : Matrix (Fin N) (Fin N) ℝ, S.IsSymm →
      ∃ (m : ℕ) (D : Circuit ((Fin N × Fin k) ⊕ Fin m)),
        ((N * k + m : ℕ) : ℝ) ≤ C * (N : ℝ) ^ 2 * ((2 : ℝ) ^ k) ^ 2 * k * Real.logb 2 ((k : ℝ) + 2) ∧
        D.depth ≤ d₀ ∧
        CleanlyImplements D ((QHat (2 ^ k) S).submatrix (decodeReg N k) (decodeReg N k)) := by sorry

end ConstDepthUnitary
