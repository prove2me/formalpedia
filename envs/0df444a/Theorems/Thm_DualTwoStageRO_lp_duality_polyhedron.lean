-- Prove2me | Theorems.Thm_DualTwoStageRO_lp_duality_polyhedron
-- name    : DualTwoStageRO.lp_duality_polyhedron
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:08.510595+00:00
-- url     : https://prove2.me/theorems/2cd7f8f9-5d77-4283-a62c-f77ff5483efc
-- title:
--   Second dualization, over the uncertain parameters: LP duality on $\mathcal U$ in the extended reals
-- statement:
--   Let $D\in\mathbb R^{p\times n_\zeta}$ and $d\in\mathbb R^p$ with $\mathcal U=\{\zeta\ge0:\ D\zeta=d\}$ nonempty. For every $c\in\mathbb R^{n_\zeta}$,
--
--   $$\sup_{\zeta\in\mathcal U}c^\top\zeta=\inf\Bigl\{d^\top\lambda:\ \lambda\in\mathbb R^p,\ \sum_{k=1}^pD_{kj}\lambda_k\ge c_j,\ j=1,\dots,n_\zeta\Bigr\}$$
--
--   in the extended reals; both sides are $+\infty$ when the right-hand set is empty.
--
--   Applied with $c_j=w^\top A_{\cdot j}(x)+\sum_{i=1}^{m_1}v_iF_{ij}(x)$, it produces the inner problem over $\lambda$ of the dualized model (6): the polyhedral structure of $\mathcal U$ appears in the linear constraints of (6).
--
--   **Formalization Note** $\lambda$ is free, as in (6). The unbounded case ($+\infty=\inf\emptyset$) is part of the statement.
--
--   Differences from the source:
--   - generalization: the coefficient vector c_j = w⊤A_·j(x) + Σ_{i≥1} v_i F_ij(x) of (6) → an arbitrary c ∈ ℝ^{nζ}; reason: the paper's use is this instance of c
--   - encoding: values possibly +∞ → EReal, inf over ∅ = ⊤; reason: Lean convention; same instances
-- source:
--   de Ruiter, Zhen, den Hertog, Technical Note—Dual Approach for Two-Stage Robust Nonlinear Optimization, Operations Research 71(5):1794–1799, 2023, doi:10.1287/opre.2022.2289 (published version, sha256 75cbce38…fe03ac), abstract, p.1794 ("then over the uncertain parameters"); (6), p.1796

import Mathlib

namespace DualTwoStageRO

open Matrix

/-- **Second dualization, over the uncertain parameters: LP duality over `U` in `EReal`.**
de Ruiter, Zhen, den Hertog, Operations Research 71(5), 2023, abstract, p.1794 ("… and then over
the uncertain parameters"); the result is the `λ`-problem of (6), p.1796, with the constraint
`Σ_{k=1}^p D_kj λ_k ≥ c_j`.

For `D ∈ ℝ^{p×nζ}`, `d ∈ ℝ^p` with `U = {ζ ≥ 0 : Dζ = d}` nonempty and every `c ∈ ℝ^{nζ}`:
`sup_{ζ∈U} c⊤ζ = inf {d⊤λ | λ ∈ ℝ^p, Σ_k D_kj λ_k ≥ c_j for all j}` in `EReal`; both sides may be
`+∞` (then the right-hand set is empty), and `λ` is free. -/
theorem lp_duality_polyhedron {nζ p : ℕ} (D : Matrix (Fin p) (Fin nζ) ℝ) (d : Fin p → ℝ)
    (hU : {ζ : Fin nζ → ℝ | 0 ≤ ζ ∧ D *ᵥ ζ = d}.Nonempty) (c : Fin nζ → ℝ) :
    (⨆ ζ ∈ {ζ : Fin nζ → ℝ | 0 ≤ ζ ∧ D *ᵥ ζ = d}, ((c ⬝ᵥ ζ : ℝ) : EReal)) =
      ⨅ lam ∈ {lam : Fin p → ℝ | ∀ j, c j ≤ ∑ k, D k j * lam k}, ((d ⬝ᵥ lam : ℝ) : EReal) := by sorry

end DualTwoStageRO
