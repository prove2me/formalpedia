-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_1_3
-- name    : ArgmaxDeFinetti.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:43:46.737963+00:00
-- url     : https://prove2.me/theorems/d566fff6-b5a7-4f78-b3fa-f62ba5ea1cfd
-- title:
--   Theorem 1.3, p.6 — $t$-site bounds $4t\sqrt{d-1}/N$ (bosonic) and $4t\sqrt{d^2-1}/N$ (exchangeable) for $2\le t\le N$
-- statement:
--   Let $d\ge2$ and $2\le t\le N$. Then:
--
--   1. every $t$-site marginal $\rho^{(t)}_N$ of a bosonic state $\rho_N\in D(\mathrm{Sym}^N(\mathbb C^d))$ has a Hartree mixture $\sigma\in\mathrm{SEP}^{(t)}_H(d)=\mathrm{conv}\{|u\rangle\langle u|^{\otimes t}:\|u\|=1\}$ with
--   $$
--   D_{\mathrm{tr}}\big(\rho^{(t)}_N,\sigma\big)\le\frac{4t\sqrt{d-1}}{N};
--   $$
--   2. every $t$-site marginal of an exchangeable state on $(\mathbb C^d)^{\otimes N}$ has a tensor-power mixture $\sigma\in\mathrm{SEP}^{(t)}_P(d)=\mathrm{conv}\{\tau^{\otimes t}:\tau\in D(\mathbb C^d)\}$ with
--   $$
--   D_{\mathrm{tr}}\big(\rho^{(t)}_N,\sigma\big)\le\frac{4t\sqrt{d^2-1}}{N}.
--   $$
--
--   Here $D_{\mathrm{tr}}=\tfrac12\|\cdot\|_1$ and the marginal is taken on the first $t$ sites. Passing from two to $t$ sites costs only a factor linear in $t$, which Theorem B.5 shows is necessary. Theorem 4.1 of the paper states the same bounds for $t\ge3$.
--
--   **Formalization Note** Both Hausdorff bounds are stated, as a conjunction, in the form "every marginal has an approximant".
--
--   Differences from the source:
--   - encoding: D^tr_H(BOS^(t)_N(d), SEP^(t)_H(d)) ≤ b (Hausdorff distance, (2.6)) → every element of BOS^(t)_N(d) has some σ ∈ SEP^(t)_H(d) at trace distance ≤ b; reason: SEP^(t)_H(d) ⊆ BOS^(t)_N(d), so D_H = sup inf (2.7); the infimum is attained on the compact set SEP^(t)_H(d); same convention as the published goal
--   - encoding: D^tr_H(EXCH^(t)_N(d), SEP^(t)_P(d)) ≤ b (Hausdorff distance, (2.6)) → every element of EXCH^(t)_N(d) has some σ ∈ SEP^(t)_P(d) at trace distance ≤ b; reason: SEP^(t)_P(d) ⊆ EXCH^(t)_N(d), so D_H = sup inf (2.7); the infimum is attained on the compact set SEP^(t)_P(d); same convention as the published goal
--   - encoding: (ℂ^d)^{⊗N}, U_π, Tr_{t+1,…,N} → matrices indexed by Fin N → Fin d, the published permOp, the partial trace over sites t+1,…,N (marginal); reason: Lean convention; the conditions quantify over every π, so the orientation of U_π is immaterial
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem 1.3, p.6 (Theorem 4.1, eqs. (4.1)–(4.2), p.30, for t ≥ 3); definitions (1.1)–(1.4), p.6, and §2.1, pp.18–19

import Mathlib
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ArgmaxDeFinetti_Supplement_sepT
import Definitions.Def_ArgmaxDeFinetti_Supplement_bosT

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem 1.3 (t-site de Finetti upper bounds)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.6 (Theorem 4.1, eqs. (4.1)–(4.2), p.30, is the
same for `t ≥ 3`). For every `d ≥ 2` and `2 ≤ t ≤ N`,
`D^tr_H(BOS^{(t)}_N(d), SEP^{(t)}_H(d)) ≤ 4t√(d − 1)/N` and `D^tr_H(EXCH^{(t)}_N(d), SEP^{(t)}_P(d)) ≤ 4t√(d² − 1)/N`.

Stated as the conjunction: every `t`-site marginal of a bosonic `N`-site state is within trace distance
`4t√(d − 1)/N` of some `σ ∈ conv{|u⟩⟨u|^{⊗t} : ∥u∥ = 1}`, and every `t`-site marginal of an exchangeable `N`-site state
is within `4t√(d² − 1)/N` of some `σ ∈ conv{ρ^{⊗t} : ρ ∈ D(ℂ^d)}`.

**Formalization Note** The `sup inf` of each Hausdorff distance (2.7) is written as existence of a minimizer, which
the compactness of the separable sets gives. `D_tr` is `½∥·∥₁`. The marginal is on the first `t` sites. -/
theorem theorem_1_3 (d t N : ℕ) (hd : 2 ≤ d) (ht : 2 ≤ t) (htN : t ≤ N) :
    (∀ τ ∈ bosT t N d, ∃ σ ∈ hartreeT (Fin d) t,
      DimFreeShadow.traceDistance τ σ ≤ 4 * t * Real.sqrt ((d : ℝ) - 1) / N) ∧
    (∀ τ ∈ exchT t N d, ∃ σ ∈ tensorPowMix (Fin d) t,
      DimFreeShadow.traceDistance τ σ ≤ 4 * t * Real.sqrt ((d : ℝ) ^ 2 - 1) / N) := by sorry

end Supplement

end ArgmaxDeFinetti
