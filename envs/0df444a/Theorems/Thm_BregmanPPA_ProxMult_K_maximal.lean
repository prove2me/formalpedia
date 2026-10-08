-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_K_maximal
-- name    : BregmanPPA.ProxMult.K_maximal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:16:16.622269+00:00
-- url     : https://prove2.me/theorems/9813f9b1-a4c1-4981-87c4-dae5eaecf5a4
-- title:
--   §5, p. 220 — the saddle operator K(x, p) = ∂ₓl × (−∂̂ₚl) is maximal monotone
-- statement:
--   Consider a problem of the form (10): $C\subseteq\mathbb R^n$ closed, nonempty and convex, $f,g_1,\dots,g_m$ proper lower semicontinuous convex and finite on $C$. Let $l$ be its Lagrangian and
--
--   $$K(x,p)=\partial_x l(x,p)\times\big(-\hat\partial_p l(x,p)\big)$$
--
--   the set-valued map on $\mathbb R^{n+m}$. Then $K$ is maximal monotone.
--
--   The paper derives this from the fact that $l$ is a closed saddle function, convex in $x$ and concave in $p$, citing Rockafellar's *Convex Analysis*, Corollary 37.5.2. Maximality is the hypothesis under which Theorem 1 is applied to $K$.
--
--   **Formalization Note** $\mathbb R^{n+m}$ is `WithLp 2 (E n × E m)`. Monotonicity and maximality are the published `IsMonotoneOp`/`IsMaximalMonotone` (graph-maximality).
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 220, §5 (K is maximal monotone [26, Corollary 37.5.2])

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_IneqMult_Program
import Definitions.Def_BregmanPPA_ProxMult_Saddle

open ThreeOpSplitting.Convergence

namespace BregmanPPA.ProxMult

/-- §5, p. 220: for a problem of the form (10), the operator
`K(x, p) = ∂ₓ l(x, p) × (−∂̂ₚ l(x, p))` on `ℝⁿ⁺ᵐ` is maximal monotone. -/
theorem K_maximal {n m : ℕ} (C : Set (BregmanPPA.IneqMult.E n)) (f : BregmanPPA.IneqMult.E n → EReal) (g : Fin m → BregmanPPA.IneqMult.E n → EReal)
    (hP : BregmanPPA.IneqMult.IsConvexProgram C f g) :
    IsMaximalMonotone (opK C f g) := by sorry

end BregmanPPA.ProxMult
