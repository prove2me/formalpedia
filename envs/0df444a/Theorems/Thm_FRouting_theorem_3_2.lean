-- Prove2me | Theorems.Thm_FRouting_theorem_3_2
-- name    : FRouting.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:09:11.648378+00:00
-- url     : https://prove2.me/theorems/7402ff08-a501-4be4-bd4b-2cd2c3a44512
-- title:
--   Theorem 3.2 — triangle inequality for the fidelity angle, cosine form
-- statement:
--   Let $\rho,\omega,\sigma$ be density matrices on the same finite space and let $F(\rho,\sigma)=\|\sqrt\rho\sqrt\sigma\|_1$. Then
--   $$F(\rho,\sigma)\ge F(\rho,\omega)F(\omega,\sigma)-\sqrt{1-F(\rho,\omega)^2}\sqrt{1-F(\omega,\sigma)^2}.$$
--
--   This is the inequality through which the bound on $F_0$ passes.
--
--   Differences from the source: none.
-- source:
--   Renard, Computational Bounds for f-Routing, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 3.2, p.14

import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_WildeQIT_fidelity

set_option autoImplicit false

namespace FRouting

open WildeQIT

/-- **Theorem 3.2 (triangle inequality for the fidelity angle, in cosine form).** Renard, *Computational Bounds for f-Routing*, arXiv:2609.40278 (held copy, sha256 4a327f29…), Theorem 3.2,
p.14: "For all states ρ, ω, σ, F(ρ, σ) ≥ F(ρ, ω)F(ω, σ) − √(1 − F(ρ, ω)²) √(1 − F(ω, σ)²)."

**Formalization Note** `F` is the root fidelity `‖√ρ√σ‖₁`. -/
theorem theorem_3_2 {n : Type} [Fintype n] [DecidableEq n] (ρ ω σ : Matrix n n ℂ)
    (hρ : PeresTerno.IsDensityMatrix ρ) (hω : PeresTerno.IsDensityMatrix ω)
    (hσ : PeresTerno.IsDensityMatrix σ) :
    rootFidelity ρ ω * rootFidelity ω σ
        - Real.sqrt (1 - rootFidelity ρ ω ^ 2) * Real.sqrt (1 - rootFidelity ω σ ^ 2)
      ≤ rootFidelity ρ σ := by sorry

end FRouting
