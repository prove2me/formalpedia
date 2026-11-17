-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_3_9
-- name    : ArgmaxDeFinetti.Supplement.theorem_3_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:44:12.145375+00:00
-- url     : https://prove2.me/theorems/21c43a82-5d81-403d-8908-c0132ff028f4
-- title:
--   Theorem 3.9, p.28 — $\mathrm{BEXT}_{n,m}(d_A,d_B)$ is within $\tfrac12\sqrt{(\min\{d_A,d_B\}-1)/(nm)}$ of $\mathrm{SEP}(d_A,d_B)$
-- statement:
--   Let $n,m,d_A,d_B\ge1$. For every two-sided Bose-symmetric extendible state $\rho\in\mathrm{BEXT}_{n,m}(d_A,d_B)$, i.e. the $A_1B_1$ marginal of a state on $\mathrm{Sym}^n(\mathbb C^{d_A})\otimes\mathrm{Sym}^m(\mathbb C^{d_B})$, there is a separable state $\sigma\in\mathrm{SEP}(d_A,d_B)$ with
--
--   $$
--   D_{\mathrm{tr}}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1\le\frac12\sqrt{\frac{\min\{d_A,d_B\}-1}{nm}} .
--   $$
--
--   Equivalently, $D^{\mathrm{tr}}_H(\mathrm{BEXT}_{n,m}(d_A,d_B),\mathrm{SEP}(d_A,d_B))$ is at most this quantity. The two block sizes $n,m$ are independent; for $d_A=1$ or $d_B=1$ the bound is $0$. This is the estimate behind the disentangler, Best Separable State and separability-testing applications of Section 5.
--
--   **Formalization Note** The Hausdorff bound is stated as the existence of an approximant for every extendible state.
--
--   Differences from the source:
--   - encoding: D^tr_H(BEXT_{n,m}(dA,dB), SEP(dA,dB)) ≤ b (Hausdorff distance, (2.6)) → every element of BEXT_{n,m}(dA,dB) has some σ ∈ SEP(dA,dB) at trace distance ≤ b; reason: SEP(dA,dB) ⊆ BEXT_{n,m}(dA,dB), so D_H = sup inf (2.7); the infimum is attained on the compact set SEP(dA,dB); same convention as the published goal
--   - encoding: ρ̃ ∈ D(Sym^n(ℂ^{dA}) ⊗ Sym^m(ℂ^{dB})); ρ̃_{A1B1} → a density operator on (ℂ^{dA})^{⊗n} ⊗ (ℂ^{dB})^{⊗m} with (U_π ⊗ I)ρ̃ = ρ̃ and (I ⊗ U_τ)ρ̃ = ρ̃ (range in Sym^n ⊗ Sym^m); the partial trace over A_2…A_n B_2…B_m; reason: a state of the subspace is its extension by zero; same convention as the base IsBosonic
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem 3.9, eq. (3.23), p.28 (= Theorem 1.4, p.7); definition (2.3), p.19

import Mathlib
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ArgmaxDeFinetti_Supplement_bext

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem 3.9 (De Finetti upper bound for two-sided Bose-symmetric extendible states)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.28,
eq. (3.23) (= Theorem 1.4, p.7). For every `n, m, dA, dB ≥ 1`,
`D^tr_H(BEXT_{n,m}(dA, dB), SEP(dA, dB)) ≤ ½ √((min{dA, dB} − 1)/(nm))`.

Stated as: for every `ρ ∈ BEXT_{n,m}(dA, dB)` there is a separable `σ ∈ SEP(dA, dB)` with
`½∥ρ − σ∥₁ ≤ ½ √((min{dA, dB} − 1)/(nm))`.

**Formalization Note** Since `SEP ⊆ BEXT_{n,m}` ((2.4)), the Hausdorff distance is `sup_ρ inf_σ`, and the infimum is
attained on the compact set `SEP`. The two block sizes `n, m` are independent; `BEXT` requires symmetric support in
each block. -/
theorem theorem_3_9 (n m dA dB : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hdA : 1 ≤ dA) (hdB : 1 ≤ dB)
    (ρ : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ) (hρ : ρ ∈ bext n m dA dB) :
    ∃ σ ∈ sepAB dA dB,
      DimFreeShadow.traceDistance ρ σ ≤
        (1 / 2) * Real.sqrt ((((min dA dB : ℕ) : ℝ) - 1) / ((n : ℝ) * m)) := by sorry

end Supplement

end ArgmaxDeFinetti
