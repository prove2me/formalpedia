-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_1_10
-- name    : ArgmaxDeFinetti.Supplement.theorem_1_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:47:32.774871+00:00
-- url     : https://prove2.me/theorems/02ca4252-b3bb-40a4-80d4-47e792ccdea1
-- title:
--   Theorem 1.10, p.11 — $\mathrm{BEXT}_{n,n}(d_A,d_B)$ is within Hilbert–Schmidt distance $O(n^{-1/2})$ of $\mathrm{SEP}(d_A,d_B)$, with a universal constant
-- statement:
--   There is a universal constant $C$ such that for all $n,d_A,d_B\ge1$ and every $\rho\in\mathrm{BEXT}_{n,n}(d_A,d_B)$ there is a separable state $\sigma\in\mathrm{SEP}(d_A,d_B)$ with
--
--   $$
--   \|\rho-\sigma\|_2\le\frac{C}{\sqrt n}.
--   $$
--
--   That is, $D^{\mathrm{HS}}_H(\mathrm{BEXT}_{n,n}(d_A,d_B),\mathrm{SEP}(d_A,d_B))=O(n^{-1/2})$ uniformly in the local dimensions (Corollary 6.13 gives the explicit bound $8\sqrt{2n-1}/n$). Theorem B.7 shows the rate is optimal when the dimensions may grow; at a fixed additive error the constant-level extension SDP is therefore polynomial in the local dimensions for Hilbert–Schmidt-bounded objectives.
--
--   **Formalization Note** $C$ is chosen before $n,d_A,d_B$.
--
--   Differences from the source:
--   - reading: = O(n^{−1/2}) with a universal implied constant → ∃ C, chosen before n, dA, dB, with the bound C/√n for every n ≥ 1; reason: "universal implied constant"; on n ≥ 1 an eventual bound and a bound for every n are the same up to C
--   - encoding: D^HS_H(BEXT_{n,n}(dA,dB), SEP(dA,dB)) ≤ b → every ρ ∈ BEXT_{n,n} has some σ ∈ SEP with ∥ρ − σ∥₂ ≤ b; reason: SEP(dA,dB) ⊆ BEXT_{n,n}(dA,dB), so D_H = sup inf (2.7); the infimum is attained on the compact set SEP(dA,dB); same convention as the published goal
--   - encoding: ρ̃ ∈ D(Sym^n(ℂ^{dA}) ⊗ Sym^m(ℂ^{dB})); ρ̃_{A1B1} → a density operator on (ℂ^{dA})^{⊗n} ⊗ (ℂ^{dB})^{⊗m} with (U_π ⊗ I)ρ̃ = ρ̃ and (I ⊗ U_τ)ρ̃ = ρ̃ (range in Sym^n ⊗ Sym^m); the partial trace over A_2…A_n B_2…B_m; reason: a state of the subspace is its extension by zero; same convention as the base IsBosonic
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem 1.10, p.11 (cf. Corollary 6.13, eq. (6.36), p.50)

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_hsDist
import Definitions.Def_ArgmaxDeFinetti_Supplement_bext

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem 1.10 (Dimension-free Hilbert–Schmidt upper bound for two-sided Bose-symmetric extendible states)**,
Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.11 (cf. Corollary 6.13, eq. (6.36), p.50). For every `n, dA, dB ≥ 1`,
`D^HS_H(BEXT_{n,n}(dA, dB), SEP(dA, dB)) = O(n^{−1/2})`, with a universal implied constant.

Stated as: there is a constant `C` such that for all `n, dA, dB ≥ 1` every `ρ ∈ BEXT_{n,n}(dA, dB)` has a separable
`σ ∈ SEP(dA, dB)` with `∥ρ − σ∥₂ ≤ C/√n`.

**Formalization Note** The universal constant `C` is quantified before `n, dA, dB`. `D_HS` is the unnormalized
`∥·∥₂` (base `hsDist`); the infimum over the compact `SEP` is attained. -/
theorem theorem_1_10 :
    ∃ C : ℝ, ∀ (n dA dB : ℕ), 1 ≤ n → 1 ≤ dA → 1 ≤ dB →
      ∀ ρ ∈ bext n n dA dB, ∃ σ ∈ sepAB dA dB, hsDist ρ σ ≤ C / Real.sqrt n := by sorry

end Supplement

end ArgmaxDeFinetti
