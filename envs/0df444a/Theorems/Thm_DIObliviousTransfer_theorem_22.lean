-- Prove2me | Theorems.Thm_DIObliviousTransfer_theorem_22
-- name    : DIObliviousTransfer.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-11T09:05:56.677256+00:00
-- url     : https://prove2.me/theorems/077b70da-0a89-45b1-984c-8ae7d9907a38
-- title:
--   Theorem 22 — selector-aware constant-threshold repetition
-- statement:
--   Let $\delta_*\in(0,1)$, $\rho\in(0,1]$ and $\gamma_{\mathrm{sel}}\in(\frac{1+\delta_*}2\rho,\rho)$. Then there are $\eta_{\mathrm{sel}},c_{\mathrm{sel}}>0$ and $n_0$ such that every allowed $n$-copy strategy with $n\ge n_0$ satisfies
--   $$\Pr\Big[\sum_iJ_i\le\rho n,\ \sum_iL_i\le\eta_{\mathrm{sel}}n,\ \sum_iJ_iW_i\ge\gamma_{\mathrm{sel}}n\Big]\le2^{-c_{\mathrm{sel}}n}.$$
--   No lower bound on $\sum_iJ_i$ is assumed.
--
--   Differences from the source:
--
--   - encoding: quantum systems and strategies in the abstract (registers, measurements, instruments) → finite-dimensional registers, matrices over finite types, POVMs and Kraus instruments; reason: Decision D2: registers are polynomial-size or finite-alphabet throughout; same instances
-- source:
--   Batra, Chen, Jain, Zhang, Robust and Leakage-Resilient Device-Independent Oblivious Transfer in MiniQCrypt, arXiv:2610.01421 (held version, sha256 8334c039f604ce147d1a21ffdf444ff4ac5d5f800a6aa57577a16a006e326a42), Theorem 22, p.62 (PDF p.64)

import Mathlib
import Definitions.Def_DIObliviousTransfer_SelectorBound

namespace DIObliviousTransfer

/-- **Theorem 22 (Selector-aware constant-threshold repetition)**, Batra, Chen, Jain, Zhang,
arXiv:2610.01421 (held version, sha256 8334c039…), p.62 (PDF p.64). For every `δ∗ ∈ (0, 1)`,
`ρ ∈ (0, 1]` and `γ_sel ∈ (((1 + δ∗)/2)ρ, ρ)` there are `η_sel, c_sel > 0` and `n₀` such that for
every allowed strategy and every `n ≥ n₀`,
`Pr[Σ_i J_i ≤ ρn, Σ_i L_i ≤ η_sel n, Σ_i J_i W_i ≥ γ_sel n] ≤ 2^{−c_sel n}` (34).
No lower bound on `Σ_i J_i` is assumed.

**Formalization Note** (decision D2). Allowed strategies are the finite-dimensional n-copy
strategies of `SelStrategy n`. -/
theorem theorem_22 (δ ρ γsel : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hγ0 : (1 + δ) / 2 * ρ < γsel) (hγ1 : γsel < ρ) :
    ∃ ηsel csel : ℝ, 0 < ηsel ∧ 0 < csel ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ S : SelStrategy n,
      selProb δ S (fun x y c a b j ah =>
        (cnt j : ℝ) ≤ ρ * n ∧ (cnt (selL x y c a b) : ℝ) ≤ ηsel * n ∧
        γsel * n ≤ (cnt (fun i => j i && selW x y c a b ah i) : ℝ))
        ≤ (2 : ℝ) ^ (-(csel * n)) := by sorry

end DIObliviousTransfer
