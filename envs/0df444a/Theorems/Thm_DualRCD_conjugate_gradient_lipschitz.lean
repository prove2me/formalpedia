-- Prove2me | Theorems.Thm_DualRCD_conjugate_gradient_lipschitz
-- name    : DualRCD.conjugate_gradient_lipschitz
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:45:39.162506+00:00
-- url     : https://prove2.me/theorems/27ddfc85-f060-4ab1-823e-e595a4aba4d7
-- title:
--   p.7 — the conjugate of a $\sigma$-strongly convex function has $1/\sigma$-Lipschitz gradient
-- statement:
--   Let $\sigma>0$ and let $g:\mathbb R^n\to\mathbb R$ be $\sigma$-strongly convex. Then:
--
--   1. for every $z$ the function $\langle z,\cdot\rangle-g$ has exactly one maximizer $x(z)$;
--   2. $g^*$ is finite with $g^*(z)=\langle z,x(z)\rangle-g(x(z))$, and it is differentiable with $\nabla g^*(z)=x(z)$;
--   3. the gradient of $g^*$ is $1/\sigma$-Lipschitz:
--   $$
--   \|x(z)-x(z')\|\le\frac1\sigma\|z-z'\|\qquad\forall z,z'.
--   $$
--
--   This is the fact behind the block Lipschitz constants $L_i=1$ of the dual smooth part.
--
--   **Formalization Note.** The conjugate is valued in the extended reals, so its gradient is that of its conversion to a real number. Clause 2 shows that the value is finite.
--
--   Differences from the source:
--   - encoding: σ-strongly convex g : ℝⁿ → ℝ (left inequality of p.4) → IsStronglyConvexGrad σ g, with Differentiable ℝ g and Mathlib's gradient; reason: Lean's gradient is 0 where g is not differentiable, so differentiability is stated
--   - encoding: ∇g* for the conjugate of p.4 → the gradient of the toReal of the EReal-valued fenchelConjugate g, with finiteness as a conclusion; reason: the published conjugate is EReal-valued; it is finite here, so toReal changes no value
--   - encoding: ∇g* is 1/σ-Lipschitz → the Lipschitz bound for the arg max map, which the conclusion identifies with ∇g*; reason: same map, and predicates avoid junk values
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, §3, p.7, and the arg max formula on p.15

import Mathlib
import Definitions.Def_DualRCD_IsStronglyConvexGrad
import Definitions.Def_DualRCD_IsConjMaximizer
import Definitions.Def_fenchelConjugate

open scoped RealInnerProductSpace

namespace DualRCD

/-- If `g` is `σ`-strongly convex, its Fenchel conjugate has `1/σ`-Lipschitz continuous gradient
(Necoara & Fercoq, arXiv:1911.06014v1, §3, p.7), and `∇g*(z) = arg max_x ⟨z, x⟩ − g(x)` (p.15).
Precisely: for every `z` the arg max exists and is unique; at the arg max `x` the conjugate takes the
finite value `⟨z, x⟩ − g(x)` and the real-valued conjugate has gradient `x` at `z`; and the arg max
map is `1/σ`-Lipschitz.

**Formalization Note.** `fenchelConjugate g` is `EReal`-valued, so its gradient is that of its
`toReal`; the second clause shows the value is finite, so `toReal` loses nothing. -/
theorem conjugate_gradient_lipschitz {n : ℕ} (σ : ℝ) (hσ : 0 < σ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : IsStronglyConvexGrad σ g) :
    (∀ z, ∃! x, IsConjMaximizer g z x) ∧
      (∀ z x, IsConjMaximizer g z x →
        ConvexOptimization.fenchelConjugate g z = ((⟪z, x⟫ - g x : ℝ) : EReal) ∧
          HasGradientAt (fun w => (ConvexOptimization.fenchelConjugate g w).toReal) x z) ∧
      ∀ z z' x x', IsConjMaximizer g z x → IsConjMaximizer g z' x' →
        ‖x - x'‖ ≤ 1 / σ * ‖z - z'‖ := by sorry

end DualRCD
