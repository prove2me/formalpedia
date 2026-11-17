-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_Supplement_theorem_6_1
-- name    : ArgmaxDeFinetti.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:46:52.793259+00:00
-- url     : https://prove2.me/theorems/9c3788ef-dea6-4a4d-b98f-53fc1cd2447f
-- title:
--   Theorem 6.1, p.40 — bosonic two-site marginals are within Hilbert–Schmidt distance $8/\sqrt{N-1}$ of $\mathrm{SEP}^{(2)}_H(d)$, for every $d$
-- statement:
--   Let $N,d\ge2$. For every bosonic state $\rho_N\in D(\mathrm{Sym}^N(\mathbb C^d))$ there is a Hartree mixture $\sigma\in\mathrm{SEP}^{(2)}_H(d)=\mathrm{conv}\{|u\rangle\langle u|^{\otimes2}:\|u\|=1\}$ with
--
--   $$
--   \big\|\rho^{(2)}_N-\sigma\big\|_2\le\frac{8}{\sqrt{N-1}} ,
--   $$
--
--   where $\|X\|_2=(\mathrm{Tr}\,X^\dagger X)^{1/2}$ is the unnormalized Hilbert–Schmidt norm. Equivalently, $D^{\mathrm{HS}}_H(\mathrm{BOS}^{(2)}_N(d),\mathrm{SEP}^{(2)}_H(d))\le8/\sqrt{N-1}$.
--
--   The bound does not depend on the local dimension $d$, in contrast to every trace-norm de Finetti bound; Theorem B.6 shows the rate $N^{-1/2}$ is optimal when $d$ may grow.
--
--   **Formalization Note** $N=2+m$ as in the published goal; the Hausdorff bound is stated as the existence of an approximant.
--
--   Differences from the source:
--   - encoding: D^HS_H(BOS^(2)_N(d), SEP^(2)_H(d)) ≤ b → every bosonic ρ_N has some σ ∈ SEP^(2)_H(d) with ∥ρ^(2)_N − σ∥₂ ≤ b; N written 2 + m; reason: SEP_H ⊆ BOS, so D_H = sup inf (2.7), attained on the compact SEP_H; same convention as the published goal
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem 6.1, eq. (6.1), p.40 (= Theorem 1.9, p.10); (2.2), p.18

import Mathlib
import Definitions.Def_ArgmaxDeFinetti_hsDist
import Definitions.Def_ArgmaxDeFinetti_IsBosonic
import Definitions.Def_ArgmaxDeFinetti_marginal2
import Definitions.Def_ArgmaxDeFinetti_hartree2

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- **Theorem 6.1 (Dimension-free bosonic Hilbert–Schmidt de Finetti upper bound)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.40, eq. (6.1)
(= Theorem 1.9, p.10). For every `N, d ≥ 2`, `D^HS_H(BOS^{(2)}_N(d), SEP^{(2)}_H(d)) ≤ 8/√(N − 1)`.

Stated as: for every bosonic `ρ_N ∈ D(Sym^N(ℂ^d))` there is a Hartree mixture `σ ∈ SEP^{(2)}_H(d)` with
`∥ρ^{(2)}_N − σ∥₂ ≤ 8/√(N − 1)`, uniformly in `d`.

**Formalization Note** `N = 2 + m`, as in the base goal `theorem_3_1`. `D_HS` is the unnormalized `∥·∥₂` (base
`hsDist`, (2.2)). The `sup inf` of the Hausdorff distance (2.7) is written as existence of a minimizer, attained on the
compact set `SEP^{(2)}_H(d)`. -/
theorem theorem_6_1 (m d : ℕ) (hd : 2 ≤ d) (ρ : Op (2 + m) d) (hρ : IsBosonic ρ) :
    ∃ σ ∈ hartree2 d, hsDist (marginal2 ρ) σ ≤ 8 / Real.sqrt (((2 + m : ℕ) : ℝ) - 1) := by sorry

end Supplement

end ArgmaxDeFinetti
