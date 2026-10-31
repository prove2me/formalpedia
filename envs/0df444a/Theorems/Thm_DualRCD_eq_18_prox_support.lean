-- Prove2me | Theorems.Thm_DualRCD_eq_18_prox_support
-- name    : DualRCD.eq_18_prox_support
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:46:38.505114+00:00
-- url     : https://prove2.me/theorems/bbe43bc8-26de-42a2-aa92-ed8864369df1
-- title:
--   (18) — the prox of a scaled support function is a projection residual
-- statement:
--   Let $X\subseteq\mathbb R^n$ be nonempty, closed and convex, and let $\alpha>0$. Then for every $y$,
--   $$
--   \operatorname{prox}_{\alpha\cdot\operatorname{supp}_X}(y)=y-\alpha\cdot\Pi_X(\alpha^{-1}\cdot y).
--   $$
--   That is, $y-\alpha\,\Pi_X(\alpha^{-1}y)$ minimizes $z\mapsto\frac12\|z-y\|^2+\alpha\cdot\operatorname{supp}_X(z)$, and it is the only minimizer.
--
--   With $\alpha=1$ this turns each RCD step into a single projection onto $X_{i_k}$, which is the explicit form (20) of the iteration.
--
--   **Formalization Note.** Both the prox and the projection are predicates, so no junk value arises. For nonempty closed convex $X$ each has exactly one solution.
--
--   Differences from the source:
--   - reading: a chain of equalities whose third line is y − α · arg max_{t∈X} ½‖α·t − y‖² → only the end-to-end identity prox_{α·supp_X}(y) = y − α·Π_X(α⁻¹y); reason: that line is a typo for arg min, since the arg max does not exist for unbounded X; the middle lines are the derivation of the end-to-end identity
--   - encoding: X closed convex, with Π_X used → X nonempty closed convex; reason: Π_X of the empty set is undefined
--   - encoding: prox as an arg min and Π_X as a map → the predicates IsProxSupp and BubeckCO.PSGD.IsEuclideanProj, with uniqueness of the minimizer as a conclusion; reason: predicates avoid junk values; a projection point exists and is unique here
--   - encoding: supp_X real-valued on its domain → EReal values; reason: supp_X is +∞ off its domain
-- source:
--   Necoara & Fercoq, Linear convergence of dual coordinate descent on non-polyhedral convex problems, arXiv:1911.06014v1, §4, p.14, display (18)

import Mathlib
import Definitions.Def_DualRCD_IsProxSupp
import Definitions.Def_BubeckCO_PSGD_IsEuclideanProj

open scoped RealInnerProductSpace

namespace DualRCD

/-- The prox of a scaled support function, display (18) of Necoara & Fercoq, arXiv:1911.06014v1, §4,
p.14: for a closed convex set `X ⊆ ℝⁿ` and `α > 0`, `prox_{α·supp_X}(y) = y − α·Π_X(α⁻¹·y)`.
That is, `y − α·Π_X(α⁻¹·y)` minimizes `z ↦ ½‖z − y‖² + α·supp_X(z)`, and it is the only minimizer.

**Formalization Note.** `X` is nonempty, as `Π_X` presupposes. The projection is the published
`BubeckCO.PSGD.IsEuclideanProj` predicate, which for nonempty closed convex `X` has exactly one
solution. -/
theorem eq_18_prox_support {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hXne : X.Nonempty)
    (hXc : IsClosed X) (hXv : Convex ℝ X) (α : ℝ) (hα : 0 < α)
    (y w : EuclideanSpace ℝ (Fin n)) (hw : BubeckCO.PSGD.IsEuclideanProj X (α⁻¹ • y) w) :
    IsProxSupp X α y (y - α • w) ∧ ∀ p, IsProxSupp X α y p → p = y - α • w := by sorry

end DualRCD
