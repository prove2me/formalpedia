-- Prove2me | Theorems.Thm_ArgmaxDeFinetti_theorem_3_1
-- name    : ArgmaxDeFinetti.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:42:55.327228+00:00
-- url     : https://prove2.me/theorems/82146d8c-4260-48a2-8145-accf4a880197
-- title:
--   Theorem 3.1 — bosonic two-site de Finetti bound $\sqrt{d-1}/(2(N-1))$
-- statement:
--   For every $N,d\ge2$,
--   $$
--   D^{\mathrm{tr}}_H\big(\mathrm{BOS}^{(2)}_N(d),\mathrm{SEP}^{(2)}_H(d)\big)\le\frac{\sqrt{d-1}}{2(N-1)} .
--   $$
--   Equivalently: for every bosonic state $\rho_N\in D(\mathrm{Sym}^N(\mathbb C^d))$ there is a Hartree mixture $\sigma\in\mathrm{SEP}^{(2)}_H(d)=\operatorname{conv}\{|u\rangle\langle u|^{\otimes2}:\|u\|=1\}$ with
--   $$
--   \tfrac12\big\|\rho^{(2)}_N-\sigma\big\|_1\le\frac{\sqrt{d-1}}{2(N-1)},
--   $$
--   where $\rho^{(2)}_N=\operatorname{Tr}_{3,\dots,N}\rho_N$ is the two-site marginal. This improves the $O(d/N)$ bound of Christandl–König–Mitchison–Renner to $O(\sqrt d/N)$.
--
--   Differences from the source:
--   - encoding: D^tr_H(BOS^(2)_N(d), SEP^(2)_H(d)) ≤ √(d−1)/(2(N−1)) → for every bosonic ρ there is σ ∈ SEP^(2)_H(d) with D_tr(ρ^(2), σ) ≤ √(d−1)/(2(N−1)); reason: SEP ⊆ BOS (p.19) makes D_H the sup–inf (2.7), and SEP is compact, so each infimum is attained; the two statements are equivalent
--   - encoding: N ≥ 2 → N = 2 + m with m : ℕ; reason: the same values of N
--   - encoding: ρ_N ∈ D(Sym^N(ℂ^d)) → density operator on (ℂ^d)^⊗N with U_π ρ = ρ for every π (IsBosonic); reason: a state on Sym^N extended by zero; exactly the states with range in Sym^N
--   - encoding: conv → convexHull ℝ in the space of matrices; reason: the same set of finite convex combinations
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorem 3.1, p.22, eq. (3.1) (= Theorem 1.1, p.6)

import Mathlib
import Definitions.Def_DimFreeShadow_traceDistance
import Definitions.Def_ArgmaxDeFinetti_IsBosonic
import Definitions.Def_ArgmaxDeFinetti_marginal2
import Definitions.Def_ArgmaxDeFinetti_hartree2

open Matrix
open scoped ComplexOrder

namespace ArgmaxDeFinetti

/-- **Theorem 3.1 (Bosonic two-site de Finetti upper bound)**, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), p.22, eq. (3.1) (= Theorem 1.1, p.6).
For every `N, d ≥ 2`, `D^tr_H(BOS^{(2)}_N(d), SEP^{(2)}_H(d)) ≤ √(d − 1)/(2(N − 1))`.

Stated as: for every bosonic state `ρ_N ∈ D(Sym^N(ℂ^d))` there is a Hartree mixture
`σ ∈ SEP^{(2)}_H(d) = conv{|u⟩⟨u|^{⊗2} : ∥u∥ = 1}` with `½ ∥ρ^{(2)}_N − σ∥₁ ≤ √(d − 1)/(2(N − 1))`.

**Formalization Note** `N = 2 + m` (so `m ≥ 0` is `N ≥ 2`). Since `SEP^{(2)}_H(d) ⊆ BOS^{(2)}_N(d)` (p.19), the Hausdorff
distance is `sup_ρ inf_σ` (2.7); the inner infimum is attained because `SEP^{(2)}_H(d)` is compact, so the bound is
equivalent to the existence of `σ` for each `ρ`. Bosonic means range in `Sym^N` (`IsBosonic`), not
permutation-invariant; `D_tr` is the published `DimFreeShadow.traceDistance`, with the factor `½` of (2.1); `∥u∥` is Euclidean. `ρ^{(2)}_N` is `Tr_{3,…,N} ρ_N`. -/
theorem theorem_3_1 (m d : ℕ) (hd : 2 ≤ d) (ρ : Op (2 + m) d) (hρ : IsBosonic ρ) :
    ∃ σ ∈ hartree2 d,
      DimFreeShadow.traceDistance (marginal2 ρ) σ ≤ Real.sqrt ((d : ℝ) - 1) / (2 * (((2 + m : ℕ) : ℝ) - 1)) := by sorry

end ArgmaxDeFinetti
