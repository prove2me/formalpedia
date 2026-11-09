-- Prove2me | Theorems.Thm_ElimAgree_corollary_3_7
-- name    : ElimAgree.corollary_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:23:21.512208+00:00
-- url     : https://prove2.me/theorems/4d629c8b-d90e-44af-973e-813d20610526
-- title:
--   Corollary 3.7 — one reference law for all answers
-- statement:
--   Let $\ell\ge1$, $N=4\ell-1$ and $k\ge1$. For $\sigma\in\{D,I\}^k$ let $\mu_\sigma=\bigotimes_i\mu_{\sigma_i}$ and $\lambda=\mu_D^{\otimes k}$. Then:
--   1. every rectangle $R$ satisfies $\mu_\sigma(R)\ge\lambda(R)-\frac{16}{\ell}J_\lambda(R)$;
--   2. for $0<\varepsilon<1$ and every rectangle $A\times B$,
--   $$\mu_\sigma(A\times B)\ge(1-\varepsilon)\,\lambda(A\times B)-e^{-\varepsilon\ell/16}\sqrt{\lambda_X(A)\,\lambda_Y(B)} .$$
--
--   Every answer pattern is compared with the single all-disjoint law.
--
--   Differences from the source:
--   - encoding: N = 4ℓ − 1 with ℓ-subsets (ℓ ≥ 1 implicit) → hypothesis 1 ≤ ℓ; reason: for ℓ = 0 there is no [N]
--   - encoding: rectangles in the r-fold input space of tuples of ℓ-subsets of [N] → rectangles of arbitrary tuples of subsets of [N]; the laws vanish off tuples of ℓ-subsets; reason: a rectangle of all subsets meets the support in a rectangle of ℓ-subsets with the same masses and marginals
--   - encoding: σ ∈ {D, I}^k → σ : Fin k → Bool with true = D; reason: Lean convention; same instances
-- source:
--   Ben Daniel, Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination, manuscript (STOC 2027 submission; held version sha256 eea57875…), Corollary 3.7, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_ElimAgree_deficit
import Definitions.Def_ElimAgree_muD

namespace ElimAgree

/-- Corollary 3.7 (One reference law for all answers), Ben Daniel, *Can Many Instances Be Cheaper Than One? The Price of Agreement in Elimination*, manuscript (STOC 2027 submission), p.10: for `k ≥ 1` and
`σ ∈ {D, I}^k` let `µ_σ = ⊗_i µ_{σ_i}` and `λ = µ_D^{⊗k}`. Every rectangle satisfies
`µ_σ(R) ≥ λ(R) − (16/ℓ) J_λ(R)`. In particular, for `0 < ε < 1`,
`µ_σ(A × B) ≥ (1 − ε) λ(A × B) − e^{−εℓ/16} √(λ_X(A) λ_Y(B))`.

**Formalization Note.** `σ : Fin k → Bool` with `true = D`. `1 ≤ ℓ` is the setting of §3.3. -/
theorem corollary_3_7 (ℓ k : ℕ) (hℓ : 1 ≤ ℓ) (hk : 1 ≤ k) (σ : Fin k → Bool) :
    (∀ A B : Finset (Fin k → Nset ℓ),
      lawRect (muSigma ℓ σ) A B ≥
        lawRect (lamD ℓ k) A B - 16 / (ℓ : ℝ) * deficit (lamD ℓ k) A B) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ A B : Finset (Fin k → Nset ℓ),
      lawRect (muSigma ℓ σ) A B ≥
        (1 - ε) * lawRect (lamD ℓ k) A B -
          Real.exp (-(ε * ℓ / 16)) * Real.sqrt (margX (lamD ℓ k) A * margY (lamD ℓ k) B)) := by sorry

end ElimAgree
