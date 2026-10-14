-- Prove2me | Theorems.Thm_CPDNetworks_Lower_step_4_cortinovis_kressner
-- name    : CPDNetworks.Lower.step_4_cortinovis_kressner
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:54.002269+00:00
-- url     : https://prove2.me/theorems/51f5103e-6f7a-4f15-93f8-d0c355b7eb83
-- title:
--   Proof of Theorem 2, Step 4 (Cortinovis–Kressner 2021, Theorem 2) — Laplace transform of a Rademacher chaos, ‖A‖_{2→2} ≤ 1
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ be a symmetric matrix with zero diagonal and spectral norm $\|A\|_{2\to2}\le1$, and let $\zeta$ be uniformly distributed on $\{-1,+1\}^n$. Then for all $0<\mu<1/4$,
--   $$\log\mathrm E\big(e^{\mu\zeta^{\mathsf T}A\zeta}\big)\ \le\ \mu\|A\|_F^2\log\frac{1-2\mu}{1-4\mu}\ \le\ \frac{2\mu^2\|A\|_F^2}{1-4\mu},$$
--   where $\|A\|_F^2=\sum_{i,j}A_{ij}^2$.
--
--   This bound on the Laplace transform of a Rademacher chaos is the tool the paper uses in Step 4 to control the right side of display (27).
--
--   **Formalization Note** The page states the inequality for every symmetric zero-diagonal $A$, without the normalisation $\|A\|_{2\to2}\le1$. As printed it is false: for $A=\mathbf 1_n\mathbf 1_n^{\mathsf T}-\mathrm{id}_n$, $n=100$, $\mu=0.05$ the left side exceeds $426$ while the right side of the first inequality is about $58$ (the left side grows like $\mu n^2$, the right like $\mu^2n^2$). The bound is not homogeneous in $A$ unless $\|A\|_{2\to2}$ is fixed, and the cited inequality of Cortinovis and Kressner involves $\|A\|_{2\to2}$; the hypothesis $\|A\|_{2\to2}\le1$ is the normalisation under which the printed form holds, and it is added and disclosed. $\mathrm E$ is the average over the $2^n$ sign vectors.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 36, proof of Theorem 2, Step 4 (Theorem 2 in Cortinovis and Kressner 2021)

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Lower_Setting

namespace CPDNetworks.Lower

open HighDimProb.RandomMatrices

/-- **Proof of Theorem 2, Step 4** (Enikeeva–Klopp, p. 36; Theorem 2 of Cortinovis and Kressner
2021): the Laplace transform of a Rademacher chaos. Let `A ∈ ℝ^{n×n}` be symmetric with zero
diagonal and `‖A‖_{2→2} ≤ 1`. Then for all `0 < μ < 1/4`,
`log E e^{μζᵀAζ} ≤ μ‖A‖_F² log((1 − 2μ)/(1 − 4μ)) ≤ 2μ²‖A‖_F²/(1 − 4μ)`, where `ζ` is uniform on
`{−1, +1}ⁿ`. The normalisation `‖A‖_{2→2} ≤ 1` is not printed on the page; without it the first
inequality fails (e.g. `A = 1_n1_nᵀ − id_n`, `μ = 0.05`, `n = 100`). -/
theorem step_4_cortinovis_kressner (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hdiag : ∀ i, A i i = 0) (hnorm : matrixOpNorm A ≤ 1) (μ : ℝ) (hμ : 0 < μ) (hμ4 : μ < 1 / 4) :
    Real.log ((2 ^ n : ℝ)⁻¹ * ∑ b : Fin n → Bool,
        Real.exp (μ * ∑ i : Fin n, ∑ j : Fin n, sgn b i * A i j * sgn b j)) ≤
        μ * (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) * Real.log ((1 - 2 * μ) / (1 - 4 * μ)) ∧
      μ * (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) * Real.log ((1 - 2 * μ) / (1 - 4 * μ)) ≤
        2 * μ ^ 2 * (∑ i : Fin n, ∑ j : Fin n, A i j ^ 2) / (1 - 4 * μ) := by sorry

end CPDNetworks.Lower
