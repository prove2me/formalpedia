-- Prove2me | Theorems.Thm_BiasVarianceMinimax_phi_asymptotics
-- name    : BiasVarianceMinimax.phi_asymptotics
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T11:31:42.618185+00:00
-- url     : https://prove2.me/theorems/55642194-8a72-4126-bf05-5544bd853836
-- title:
--   p.53 — asymptotics of $\phi$
-- statement:
--   With $\phi(\kappa)=\sum_{j=1}^n (j+n_0)^{-\kappa}$, as $n\to\infty$,
--
--   $$\phi(1)\sim\log n,\qquad \phi(\kappa)\sim\frac1{1-\kappa}\,n^{1-\kappa}\quad(\kappa<1).$$
--
--   The entries of $\Xi$ inherit their scales from these two sums.
--
--   Differences from the source:
--   - generalization: the page's φ has n₀ = 0 → every n₀ ∈ ℕ; reason: specializes to the page at n₀ = 0; Theorem 8 needs n₀
-- source:
--   Lam, Zhang & Zhang, arXiv:1902.04673v1, p.53; p.21

import Mathlib
import Definitions.Def_BiasVarianceMinimax_xi

open Filter Asymptotics

namespace BiasVarianceMinimax

/-- **Asymptotics of `φ`.** Lam, Zhang & Zhang, arXiv:1902.04673v1, p.53 (the same claim on p.21):
`φ(1) ∼ log n` and `φ(κ) ∼ n^(1-κ)/(1-κ)` for `κ < 1`.

**Formalization Note.** With the shift `n₀`, which the page sets to `0`, and for every real
`κ < 1`. -/
theorem phi_asymptotics (n₀ : ℕ) :
    (fun n : ℕ => phi n₀ n 1) ~[atTop] (fun n : ℕ => Real.log (n : ℝ)) ∧
    ∀ κ : ℝ, κ < 1 →
      (fun n : ℕ => phi n₀ n κ) ~[atTop] (fun n : ℕ => 1 / (1 - κ) * (n : ℝ) ^ (1 - κ)) := by sorry

end BiasVarianceMinimax
