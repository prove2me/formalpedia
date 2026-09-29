-- Prove2me | Theorems.Thm_ClarkeGradients_MaxFunctions_mem_generalizedGradient_of_le_limsup
-- name    : ClarkeGradients.MaxFunctions.mem_generalizedGradient_of_le_limsup
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:42:38.533319+00:00
-- url     : https://prove2.me/theorems/538f7de5-64cc-40da-bf68-ded54b1ac54c
-- title:
--   Corollary (1.10) — a lower bound on one-sided quotients gives membership in ∂f(x)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be locally Lipschitz and $x,\zeta\in\mathbb R^n$. If for every $v\in\mathbb R^n$
--
--   $$
--   \zeta\cdot v\le\limsup_{\delta\downarrow 0}\frac{f(x+\delta v)-f(x)}{\delta},
--   $$
--
--   then $\zeta\in\partial f(x)$.
--
--   This criterion is how the inclusion (2.2) in the proof of Theorem (2.1) is obtained: the generalized gradients of the active pieces $g(\cdot,u)$, $u\in M(x)$, are shown to lie in $\partial f(x)$.
--
--   **Formalization Note** The upper limit is `Filter.limsup` in $\mathbb R$ along $\mathcal N_{>}(0)$; it is a genuine upper limit because the quotient is bounded for locally Lipschitz $f$ (the hypothesis `hf`, the §1 standing assumption).
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 249, Corollary (1.10)

import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient

open Filter Topology

namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Corollary (1.10): for locally Lipschitz `f`, if
`ζ · v ≤ limsup_{δ ↓ 0} [f(x + δv) - f(x)] / δ` for all `v ∈ ℝⁿ`, then `ζ ∈ ∂f(x)`. -/
theorem mem_generalizedGradient_of_le_limsup {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Shared.LipschitzOnBounded f) (x ζ : EuclideanSpace ℝ (Fin n))
    (h : ∀ v : EuclideanSpace ℝ (Fin n),
      inner ℝ ζ v ≤ limsup (fun δ : ℝ => (f (x + δ • v) - f x) / δ) (𝓝[>] (0 : ℝ))) :
    ζ ∈ Shared.generalizedGradient f x := by sorry

end ClarkeGradients.MaxFunctions
