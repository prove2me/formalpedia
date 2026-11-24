-- Prove2me | Theorems.Thm_EkelandVP_Constraints_Supplement_palais_smale_existence
-- name    : EkelandVP.Constraints.Supplement.palais_smale_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:25:49.375092+00:00
-- url     : https://prove2.me/theorems/ea8ab179-b34a-4c8e-ab60-74509b3bb96c
-- title:
--   Palais–Smale Existence Theorem (corrected: the greatest lower bound is attained on every connected component)
-- statement:
--   Let $M$ be a complete strong smooth Riemannian manifold modeled on a real Hilbert space $H$ (possibly infinite dimensional), and let $F:M\to\mathbb R$ be a $C^1$ function, bounded below on $M$, satisfying the paper's **condition (C)**: for every subset $S\subseteq M$ on which $|F|$ is bounded but $\|\operatorname{grad}F\|$ is not bounded away from zero, there is a critical point of $F$ in the closure $\overline S$. Then for every point $x_0\in M$, with $C(x_0)$ its connected component,
--   $$
--   \exists x\in C(x_0)\ \forall y\in C(x_0),\qquad F(x)\le F(y),
--   $$
--   that is, $F$ attains its greatest lower bound on every connected component. When $M$ is connected this is exactly the printed conclusion: $F$ assumes its greatest lower bound on $M$.
--
--   **Formalization Note** The printed theorem quantifies over every complete Riemannian manifold, and §5 (p.339) defines the intrinsic distance only between points of the same component, so disconnected manifolds are included. On such manifolds the printed conclusion is false: on countably many components with $F\equiv 1/(n+1)$ on the $n$th one, every point is critical, the literal condition (C) holds, and the infimum $0$ is not attained (stated as `palais_smale_counterexample`; see DISPROOF.md). The componentwise conclusion is the corrected statement: it coincides with the printed one on every connected manifold (the setting §6 adopts) and remains true on every component of a disconnected one, because each component is open and closed, hence itself a connected complete Riemannian manifold on which $F$ satisfies (C). Condition (C) is kept in its literal subset/closure form, not replaced by sequential Palais–Smale compactness. A base point $x_0$ supplies the nonemptiness the printed statement takes for granted.
--
--   Differences from the source:
--   - correction: $F$ assumes its greatest lower bound on $M$ → $F$ attains its greatest lower bound on the connected component of every point; reason: the printed claim is false on disconnected complete manifolds (DISPROOF.md); the corrected claim equals the printed one whenever $M$ is connected
-- source:
--   Ekeland, On the Variational Principle, J. Math. Anal. Appl. 47 (1974), p. 340, Palais–Smale Existence Theorem, with condition (C) (PDF 17); proof p. 341 (PDF 18); https://doi.org/10.1016/0022-247X(74)90025-0

import Mathlib
import Definitions.Def_EkelandVP_Constraints_Supplement_riemannianManifold
import Definitions.Def_EkelandVP_Constraints_Supplement_conditionC
set_option autoImplicit false

open Manifold Bundle
open scoped ContDiff Bundle

namespace EkelandVP.Constraints.Supplement

/-- Corrected Palais–Smale existence theorem: a bounded-below C¹ function satisfying the
literal condition (C) attains its greatest lower bound on every connected component.
On a connected manifold this is the printed conclusion; the componentwise form is what
survives the disconnected counterexample `palais_smale_counterexample`. -/
theorem palais_smale_existence (D : CompleteStrongRiemannian) (F : D.M → ℝ)
    (hF : ContMDiff 𝓘(ℝ, D.H) 𝓘(ℝ) 1 F)
    (hC : ConditionC F (differentialNorm D F))
    (hbdd : BddBelow (Set.range F)) (x₀ : D.M) :
    ∃ x ∈ connectedComponent x₀, ∀ y ∈ connectedComponent x₀, F x ≤ F y := by sorry

end EkelandVP.Constraints.Supplement
