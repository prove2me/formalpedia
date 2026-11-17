-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_1_2
-- name    : ArgmaxDeFinetti.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:43:08.999039+00:00
-- url     : https://prove2.me/theorems/10012a05-5349-475d-8450-99289e96443c
-- title:
--   Theorem 1.2, p.6 — exchangeable two-site marginals are within $\sqrt{d^2-1}/(2(N-1))$ of $\mathrm{SEP}^{(2)}_P(d)$
-- statement:
--   Let $N,d\ge2$. Let $\rho_N$ be an **exchangeable** state on $(\mathbb C^d)^{\otimes N}$, i.e. a density operator with $U_\pi\rho_NU_\pi^\dagger=\rho_N$ for all $\pi\in S_N$, and let $\rho^{(2)}_N$ be its marginal on the first two sites. Then there is a tensor-power mixture $\sigma\in\mathrm{SEP}^{(2)}_P(d)=\mathrm{conv}\{\tau\otimes\tau:\tau\in D(\mathbb C^d)\}$ with
--
--   $$
--   D_{\mathrm{tr}}\big(\rho^{(2)}_N,\sigma\big)=\tfrac12\big\|\rho^{(2)}_N-\sigma\big\|_1\le\frac{\sqrt{d^2-1}}{2(N-1)} .
--   $$
--
--   Equivalently, $D^{\mathrm{tr}}_H\big(\mathrm{EXCH}^{(2)}_N(d),\mathrm{SEP}^{(2)}_P(d)\big)\le\sqrt{d^2-1}/(2(N-1))$. This is the exchangeable counterpart of the published bosonic goal (Theorem 3.1), with $d^2$ in place of $d$ under the root; the rectangular Werner examples show the order $d/N$ cannot be improved.
--
--   **Formalization Note** The Hausdorff bound is stated as the existence of an approximant for every marginal.
--
--   Differences from the source:
--   - encoding: D^tr_H(EXCH^(2)_N(d), SEP^(2)_P(d)) ≤ b (Hausdorff distance, (2.6)) → every element of EXCH^(2)_N(d) has some σ ∈ SEP^(2)_P(d) at trace distance ≤ b; reason: SEP^(2)_P(d) ⊆ EXCH^(2)_N(d), so D_H = sup inf (2.7); the infimum is attained on the compact set SEP^(2)_P(d); same convention as the published goal
--   - encoding: (ℂ^d)^{⊗N}, U_π, Tr_{t+1,…,N} → matrices indexed by Fin N → Fin d, the published permOp, the partial trace over sites t+1,…,N (marginal); reason: Lean convention; the conditions quantify over every π, so the orientation of U_π is immaterial
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem 1.2, p.6 (= Corollary 3.7, eq. (3.22), p.27); definitions (1.2), (1.4), p.6, and §2.1, pp.18–19

import Mathlib
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ArgmaxDeFinetti_Supplement_sepT
import Definitions.Def_ArgmaxDeFinetti_Supplement_bosT

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem 1.2 (Exchangeable two-site de Finetti upper bound)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.6 (= Corollary 3.7, eq. (3.22),
p.27). For every `N, d ≥ 2`, `D^tr_H(EXCH^{(2)}_N(d), SEP^{(2)}_P(d)) ≤ √(d² − 1)/(2(N − 1))`.

Stated as: for every two-site marginal `τ` of an exchangeable `N`-site state on `(ℂ^d)^{⊗N}` there is a
tensor-power mixture `σ ∈ conv{ρ ⊗ ρ : ρ ∈ D(ℂ^d)}` with `½∥τ − σ∥₁ ≤ √(d² − 1)/(2(N − 1))`.

**Formalization Note** Since `SEP^{(2)}_P(d) ⊆ EXCH^{(2)}_N(d)` (p.19), the Hausdorff distance is `sup_τ inf_σ`
(2.7); the infimum is attained because `SEP^{(2)}_P(d)` is compact, so the bound is equivalent to the existence of
`σ` for each `τ` (the base goal's convention). Exchangeable means `U_π ρ U_π† = ρ` (not bosonic). -/
theorem theorem_1_2 (N d : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (τ : Op 2 d) (hτ : τ ∈ exchT 2 N d) :
    ∃ σ ∈ tensorPowMix (Fin d) 2,
      DimFreeShadow.traceDistance τ σ ≤ Real.sqrt ((d : ℝ) ^ 2 - 1) / (2 * ((N : ℝ) - 1)) := by sorry

end Supplement

end ArgmaxDeFinetti
