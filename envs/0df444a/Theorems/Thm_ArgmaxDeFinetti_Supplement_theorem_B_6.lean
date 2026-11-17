-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_B_6
-- name    : ArgmaxDeFinetti.Supplement.theorem_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:48:49.116653+00:00
-- url     : https://prove2.me/theorems/e360650d-10f7-4284-a34b-df5d516a7830
-- title:
--   Theorem B.6, p.66 — $\sup_{d\ge2}D^{\mathrm{HS}}_H(\mathrm{BOS}^{(2)}_N(d),\mathrm{SEP}^{(2)}_H(d))=\Omega(N^{-1/2})$
-- statement:
--   There are a constant $c>0$ and an $N_0$ such that for every $N\ge N_0$ there are a dimension $d\ge2$ and a bosonic state $\rho_N\in D(\mathrm{Sym}^N(\mathbb C^d))$ whose two-site marginal satisfies
--
--   $$
--   \big\|\rho^{(2)}_N-\sigma\big\|_2\ge\frac{c}{\sqrt N}\qquad\text{for every }\sigma\in\mathrm{SEP}^{(2)}_H(d).
--   $$
--
--   Equivalently, as $N\to\infty$, $\sup_{d\ge2}D^{\mathrm{HS}}_H(\mathrm{BOS}^{(2)}_N(d),\mathrm{SEP}^{(2)}_H(d))=\Omega(N^{-1/2})$. This shows that the dimension-free rate $8/\sqrt{N-1}$ of Theorem 6.1 is optimal when the local dimension may grow.
--
--   **Formalization Note** $N=2+m$; the dimension $d$ may depend on $N$.
--
--   Differences from the source:
--   - reading: as N → ∞, sup_{d≥2} D^HS_H(BOS^(2)_N(d), SEP^(2)_H(d)) = Ω(N^{−1/2}) → ∃ c > 0, N₀ such that ∀ N ≥ N₀ ∃ d ≥ 2 ∃ bosonic ρ_N ∀ σ ∈ SEP^(2)_H(d), ∥ρ^(2)_N − σ∥₂ ≥ c/√N; reason: equivalent up to the constant: a supremum (bounded by √2) of sup–inf values exceeds c'/√N iff some d and ρ have every σ at distance ≥ c/√N for any c < c'
--   - encoding: N → 2 + m; reason: same convention as the published goal
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem B.6, p.66

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_hsDist
import Definitions.Def_ArgmaxDeFinetti_IsBosonic
import Definitions.Def_ArgmaxDeFinetti_marginal2
import Definitions.Def_ArgmaxDeFinetti_hartree2

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem B.6 (Dimension-free bosonic Hilbert–Schmidt lower bound)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.66. As `N → ∞`,
`sup_{d ≥ 2} D^HS_H(BOS^{(2)}_N(d), SEP^{(2)}_H(d)) = Ω(N^{−1/2})`.

Stated as: there are `c > 0` and `N₀` such that for every `N ≥ N₀` some `d ≥ 2` and some bosonic
`ρ_N ∈ D(Sym^N(ℂ^d))` have `∥ρ^{(2)}_N − σ∥₂ ≥ c/√N` for every Hartree mixture `σ ∈ SEP^{(2)}_H(d)`.

**Formalization Note** `N = 2 + m`. The supremum over `d` of `sup_ρ inf_σ` is `≥ c'/√N` for all large `N` iff the
displayed existence holds for all large `N` with some `c > 0` (take `c < c'`); the values are bounded by `√2`, so the
supremum is a real number. `d` is not fixed: it may depend on `N`. `D_HS` is the unnormalized `∥·∥₂`. -/
theorem theorem_B_6 :
    ∃ (c : ℝ) (N₀ : ℕ), 0 < c ∧ ∀ m : ℕ, N₀ ≤ 2 + m →
      ∃ d : ℕ, 2 ≤ d ∧ ∃ ρ : Op (2 + m) d, IsBosonic ρ ∧
        ∀ σ ∈ hartree2 d, c / Real.sqrt ((2 + m : ℕ) : ℝ) ≤ hsDist (marginal2 ρ) σ := by sorry

end Supplement

end ArgmaxDeFinetti
