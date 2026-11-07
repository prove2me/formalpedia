-- Prove2me | Theorems.Thm_ErasureQTanner_theorem_4
-- name    : ErasureQTanner.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:03:21.063806+00:00
-- url     : https://prove2.me/theorems/34808d60-a50c-48a5-8973-aa51179d3406
-- title:
--   Theorem 4 — linear-time decoder for low-weight errors
-- statement:
--   There is an absolute $a_0>0$ such that, for $\delta,\kappa>0$ and $\Delta$ large enough, every quantum Tanner code as in Theorem 3 admits a linear-time decoder: on a word RAM with $O(\log|G|)$-bit words, one program takes the syndromes of errors $e_X,e_Z$ of weight at most $a_0\delta^2\kappa^3N/\Delta$ and returns, within $O(N)$ steps, estimates in the correct cosets $e_Z+C_Z^\perp$, $e_X+C_X^\perp$. Corollary 5 of the paper is the instance with $\delta,\kappa$ determined by $\rho,\varepsilon$.
--
--   Differences from the source:
--   - reading: "linear-time" → one program, $b$, $T$ fixed before the group; at most $TN$ steps on `TrulySubcubicAPSP` with $W\ge b(\lfloor\log_2|G|\rfloor+1)$; reason: the paper names no machine; the word RAM is what its look-ups need
--   - generalization: "any error pattern of weight at most $a\delta^2\kappa^3N/\Delta$" → each of $e_X$, $e_Z$ separately has at most this weight; reason: an error whose union or summed weight is within the bound has both components within it, so every error of the source is covered (and the sum form used on p.28)
--   - reading: "Ramanujan", robustness of the codes → non-bipartite Ramanujan; the eight pairs of `GoodLocal`; reason: as in Theorem 3
-- source:
--   H. D. Pfister, O. Sprumont, G. Zémor, Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels, STOC 2027 submission (manuscript sha256 bf7a84a5…), Theorem 4, p.8; Corollary 5, p.9

import Mathlib
import Definitions.Def_ErasureQTanner_HX
import Definitions.Def_ErasureQTanner_inputWords

set_option autoImplicit false

namespace ErasureQTanner

/-- **Theorem 4** (with Corollary 5, p.9). Pfister, Sprumont, Zémor, *Classical Tensor Codes and Quantum Tanner Codes Achieve Capacity on Erasure Channels*, STOC 2027 submission (manuscript sha256 bf7a84a5…), p.8: "For a large enough constant `∆`, the quantum Tanner code admits a linear-time decoding algorithm that
decodes any error pattern of weight at most `aδ²κ³N/∆`, for some absolute constant `a`."

**Formalization Note.** "Linear-time" is on the published word RAM `TrulySubcubicAPSP`: one program `P`, word-size constant `b` and time
constant `T`, fixed before the group, serve every Ramanujan complex at every word size `W ≥ b(⌊log₂|G|⌋ + 1)`. `P` is given the syndromes and may ignore the
pattern `x`, so `x` is free. The bound is per component, which implies the sum form used on p.28. Corollary 5 is the instance `f := a₀δ²κ³`, with `δ`, `κ` from the local
codes. -/
theorem theorem_4 : ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ δ κ : ℝ, 0 < δ → 0 < κ →
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∀ L : LocalCodes Δ, GoodLocal δ κ L.CA L.CB L.DA L.DB →
    ∃ (P : List TrulySubcubicAPSP.Instr) (b T : ℕ), ∀ Γ : LRData Δ, Γ.IsRamanujan →
    ∀ (eX eZ : Γ.Square → ZMod 2),
      (hammingNorm eX : ℝ) ≤ a₀ * δ ^ 2 * κ ^ 3 * Γ.N / Δ →
      (hammingNorm eZ : ℝ) ≤ a₀ * δ ^ 2 * κ ^ 3 * Γ.N / Δ →
    ∀ (x : Γ.Square → Bool) (W : ℕ), b * (Nat.log2 (Fintype.card Γ.G) + 1) ≤ W →
      ∃ (t : ℕ) (e'X e'Z : Γ.Square → ZMod 2), t ≤ T * Γ.N ∧ RunOutput Γ L P W t x eX eZ e'X e'Z ∧
        e'Z + eZ ∈ checkRows (HZ Γ L) ∧ e'X + eX ∈ checkRows (HX Γ L) := by sorry

end ErasureQTanner
