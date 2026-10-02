-- Prove2me | Theorems.Thm_DiscreteConvex_LConvexFunctionsC_submodular_local_criterion_pairwise
-- name    : DiscreteConvex.LConvexFunctionsC.submodular_local_criterion_pairwise
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T00:35:20.126862+00:00
-- url     : https://prove2.me/theorems/d2c264ca-0897-446b-8bf3-f1805b5b8b0d
-- title:
--   Proposition 7.24 -- submodular_local_criterion_pairwise
-- statement:
--   **Proposition 7.24** (p.190), part (1). Let $g:\mathbb R^V\to\mathbb R\cup\{+\infty\}$ have an interval effective domain. Then $g$ is submodular (SBF[R]) if $g(p+\lambda\chi_u)+g(p+\mu\chi_v)\ge g(p)+g(p+\lambda\chi_u+\mu\chi_v)$ (Eq. (7.30)) for all $p\in\operatorname{dom}_{\mathbb R} g$, $u\ne v\in V$, and $\lambda,\mu\in\mathbb R_+$.
--
--   **Formalization Note.** Part (2), the sharper sufficient condition restricting $\lambda,\mu$ to sorted-gap ranges $[0,\hat p_{i-1}-\hat p_i]$, is not restated here: it needs the same sorted-distinct-value indexing this chunk builds for Proposition 7.25, applied to a second, unrelated purpose, and no other result in this chunk needs it. See `MODERATION_NOTES.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, Proposition 7.24.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.190, Proposition 7.24

import Mathlib
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_DomR
import Definitions.Def_DiscreteConvex_LConvexFunctionsC_SBFR

namespace DiscreteConvex.LConvexFunctionsC

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 7.24 (p.190), part (1). A sufficient pairwise-perturbation criterion for
submodularity on an interval domain. -/
theorem submodular_local_criterion_pairwise (g : (V → ℝ) → WithTop ℝ) (hint : (DomR g).OrdConnected)
    (hpair : ∀ u v : V, u ≠ v → ∀ p ∈ DomR g, ∀ lam mu : ℝ, 0 ≤ lam → 0 ≤ mu →
      g (fun w => p w + lam * (if w = u then 1 else 0)) +
        g (fun w => p w + mu * (if w = v then 1 else 0)) ≥
      g p + g (fun w => p w + lam * (if w = u then 1 else 0) + mu * (if w = v then 1 else 0))) :
    SBFR g := by sorry

end DiscreteConvex.LConvexFunctionsC
