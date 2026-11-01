-- Prove2me | Theorems.Thm_CVStabilizer_omega_span_eq_zero
-- name    : CVStabilizer.omega_span_eq_zero
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:04.657792+00:00
-- url     : https://prove2.me/theorems/e39f0ed2-f86f-48ed-9ba3-8aca831e9e42
-- title:
--   Eq. (5): the span of pairwise symplectically orthogonal vectors is isotropic
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb R^{2n}$ satisfy $\omega(u_i,u_j)=0$ for all $i,j$. If $v=\sum_i a_iu_i$ and $v'=\sum_i a'_iu_i$ with real coefficients, then
--
--   $$
--   \omega(v,v')=\sum_{i,j}a_ia'_j\,\omega(u_i,u_j)=0 .
--   $$
--
--   That is, the real span $W$ of the $u_i$ is an isotropic subspace. Together with (3) this is why the subgroup $S$ of (4) is abelian.
--
--   **Formalization Note** The span is Mathlib's real `Submodule.span`; linear independence of the $u_i$ is not needed.
--
--   Differences from the source: none.
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, eq. (5), p.1

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **Isotropy of the span, (5)**, Barnes, arXiv:quant-ph/0405064v1, p.1: if `ω(uᵢ, uⱼ) = 0` for
all `i, j`, `v = Σᵢ aᵢuᵢ` and `v′ = Σᵢ a′ᵢuᵢ`, then
`ω(v, v′) = Σᵢⱼ aᵢa′ⱼ ω(uᵢ, uⱼ) = 0`. The real span of the `uᵢ` is isotropic.

**Formalization Note** Linear independence of the `uᵢ` is not needed here and is not assumed. -/
theorem omega_span_eq_zero (n k : ℕ) (u : Fin k → PhaseSpace n)
    (hiso : ∀ i j, omega n (u i) (u j) = 0) :
    ∀ v ∈ Submodule.span ℝ (Set.range u), ∀ v' ∈ Submodule.span ℝ (Set.range u),
      omega n v v' = 0 := by sorry

end CVStabilizer
