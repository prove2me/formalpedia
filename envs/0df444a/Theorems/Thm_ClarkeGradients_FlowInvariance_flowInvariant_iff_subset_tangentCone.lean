-- Prove2me | Theorems.Thm_ClarkeGradients_FlowInvariance_flowInvariant_iff_subset_tangentCone
-- name    : ClarkeGradients.FlowInvariance.flowInvariant_iff_subset_tangentCone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T22:53:55.69926+00:00
-- url     : https://prove2.me/theorems/03e3414d-7683-4107-856f-3101b58ff74e
-- title:
--   Theorem (4.4) — F is flow-invariant for Lipschitz X iff X(x) ⊆ T_F(x) on F
-- statement:
--   Let $X$ be a multifunction from $\mathbb R^n$ to $\mathbb R^n$ whose values $X(x)$ are nonempty and compact, and suppose $X$ is Lipschitz in the sense of (4.2). Let $F$ be a nonempty closed subset of $\mathbb R^n$. The following are equivalent:
--
--   1. $F$ is flow-invariant for $X$ (4.3): every trajectory (4.1) of $\dot x\in X(x)$ starting in $F$ stays in $F$ on $[0,1]$;
--   2. for each $x\in F$, $X(x)$ is tangent to $F$ at $x$:
--   $$X(x)\subseteq T_F(x)\qquad\text{for all } x\in F,$$
--   where $T_F(x)$ is the Clarke tangent cone (3.6).
--
--   The theorem shows that Clarke's tangent cone is exactly the right notion of tangency for invariance of closed sets under Lipschitz differential inclusions; it contains the classical invariance theorems of Bony and Brezis for Lipschitz vector fields.
--
--   **Formalization Note** "$X(x)$ nonempty and compact for every $x$" is the standing assumption stated once at the top of §4 (p. 259) and is an explicit hypothesis. Trajectories are absolutely continuous on $[0,1]$ with $\dot x(t)\in X(x(t))$ almost everywhere, encoded with `HasDerivAt`. $T_F$ is the Clarke tangent cone (the polar of the normal cone (3.1)), not Mathlib's Bouligand `tangentConeAt`. The Lipschitz constant in (4.2) is global.
-- source:
--   Clarke, Generalized gradients and applications, Trans. Amer. Math. Soc. 205 (1975), p. 260, Theorem (4.4)

import Mathlib
import Definitions.Def_ClarkeGradients_FlowInvariance_tangentCone
import Definitions.Def_ClarkeGradients_FlowInvariance_IsLipschitzMultifunction
import Definitions.Def_ClarkeGradients_FlowInvariance_FlowInvariant

namespace ClarkeGradients.FlowInvariance

/-- Clarke (1975), Theorem (4.4): let `X` be a Lipschitz multifunction (4.2) whose values `X(x)`
are nonempty and compact (standing assumption of §4), and let `F` be a nonempty closed subset of
`ℝⁿ`. Then `F` is flow-invariant for `X` (4.3) if and only if `X(x) ⊆ T_F(x)` for every `x ∈ F`,
where `T_F(x)` is the Clarke tangent cone (3.6). -/
theorem flowInvariant_iff_subset_tangentCone {n : ℕ}
    (X : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hX : ∀ x, (X x).Nonempty ∧ IsCompact (X x)) (hLip : IsLipschitzMultifunction X)
    (F : Set (EuclideanSpace ℝ (Fin n))) (hF : F.Nonempty) (hFc : IsClosed F) :
    FlowInvariant X F ↔ ∀ x ∈ F, X x ⊆ tangentCone F x := by sorry

end ClarkeGradients.FlowInvariance
