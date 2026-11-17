-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_B_7
-- name    : ArgmaxDeFinetti.Supplement.theorem_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:49:23.890386+00:00
-- url     : https://prove2.me/theorems/76023ab4-6a99-4e04-aeba-04474d4634e7
-- title:
--   Theorem B.7, p.68 — $\sup_{d\ge2}D^{\mathrm{HS}}_H(\mathrm{BEXT}_{n,n}(d,d),\mathrm{SEP}(d,d))=\Omega(n^{-1/2})$
-- statement:
--   There are a constant $c>0$ and an $n_0\ge1$ such that for every $n\ge n_0$ there are a dimension $d\ge2$ and a two-sided Bose-symmetric extendible state $\rho\in\mathrm{BEXT}_{n,n}(d,d)$ with
--
--   $$
--   \|\rho-\sigma\|_2\ge\frac{c}{\sqrt n}\qquad\text{for every }\sigma\in\mathrm{SEP}(d,d).
--   $$
--
--   Equivalently, as $n\to\infty$, $\sup_{d\ge2}D^{\mathrm{HS}}_H(\mathrm{BEXT}_{n,n}(d,d),\mathrm{SEP}(d,d))=\Omega(n^{-1/2})$, so the rate of Theorem 1.10 is optimal when the local dimensions may grow.
--
--   **Formalization Note** The dimension $d$ may depend on $n$; $n_0\ge1$ keeps $n$ in the range $n\ge1$ on which $\mathrm{BEXT}_{n,n}$ is defined.
--
--   Differences from the source:
--   - reading: as n → ∞, sup_{d≥2} D^HS_H(BEXT_{n,n}(d,d), SEP(d,d)) = Ω(n^{−1/2}) → ∃ c > 0, n₀ ≥ 1 such that ∀ n ≥ n₀ ∃ d ≥ 2 ∃ ρ ∈ BEXT_{n,n}(d,d) ∀ σ ∈ SEP(d,d), ∥ρ − σ∥₂ ≥ c/√n; reason: equivalent up to the constant, as in Theorem B.6
--   - encoding: ρ̃ ∈ D(Sym^n(ℂ^{dA}) ⊗ Sym^m(ℂ^{dB})); ρ̃_{A1B1} → a density operator on (ℂ^{dA})^{⊗n} ⊗ (ℂ^{dB})^{⊗m} with (U_π ⊗ I)ρ̃ = ρ̃ and (I ⊗ U_τ)ρ̃ = ρ̃ (range in Sym^n ⊗ Sym^m); the partial trace over A_2…A_n B_2…B_m; reason: a state of the subspace is its extension by zero; same convention as the base IsBosonic
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem B.7, p.68

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_hsDist
import Definitions.Def_ArgmaxDeFinetti_Supplement_bext

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem B.7 (Hilbert–Schmidt lower bound for two-sided Bose-symmetric extendible states)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.68.
As `n → ∞`, `sup_{d ≥ 2} D^HS_H(BEXT_{n,n}(d, d), SEP(d, d)) = Ω(n^{−1/2})`.

Stated as: there are `c > 0` and `n₀ ≥ 1` such that for every `n ≥ n₀` some `d ≥ 2` and some `ρ ∈ BEXT_{n,n}(d, d)`
have `∥ρ − σ∥₂ ≥ c/√n` for every separable `σ ∈ SEP(d, d)`.

**Formalization Note** As in Theorem B.6, the eventual `Ω` lower bound on the supremum over `d` is equivalent to the
displayed existence with some `c > 0`; `d` may depend on `n`. `n₀ ≥ 1` keeps `n ≥ 1`, the range on which
`BEXT_{n,n}` is defined. `D_HS` is the unnormalized `∥·∥₂`. -/
theorem theorem_B_7 :
    ∃ (c : ℝ) (n₀ : ℕ), 0 < c ∧ 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∃ d : ℕ, 2 ≤ d ∧ ∃ ρ ∈ bext n n d d, ∀ σ ∈ sepAB d d, c / Real.sqrt n ≤ hsDist ρ σ := by sorry

end Supplement

end ArgmaxDeFinetti
