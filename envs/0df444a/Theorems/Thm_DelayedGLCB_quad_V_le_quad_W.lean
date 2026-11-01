-- Prove2me | Theorems.Thm_DelayedGLCB_quad_V_le_quad_W
-- name    : DelayedGLCB.quad_V_le_quad_W
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T08:26:55.99853+00:00
-- url     : https://prove2.me/theorems/44f04606-10cf-4fdd-9306-72e288f1d076
-- title:
--   Proof of Theorem 1, p.26 — $\|v\|^2_{V_t}\le\|v\|^2_{W_t}+G_t\|v\|^2$
-- statement:
--   Run DUCB-GLCB and fix an outcome at which every feature vector lies in the unit ball. For every round $t$ and every $v\in\mathbb R^d$,
--   $$
--   v'V_tv=v'W_tv+\sum_{s\in M_t}(v'X_s)^2\qquad\text{and}\qquad v'V_tv\le v'W_tv+G_t\|v\|^2,
--   $$
--   where $M_t$ is the set of rounds whose reward is still missing and $G_t=|M_t|$.
--
--   The missing samples enlarge the design matrix by at most $G_t$ in every direction. This is where the $\sqrt{G_t}$ term of $\beta_t$ comes from.
--
--   Differences from the source:
--   - generalization: v = ∆_t = θ̂_t − θ* → any v ∈ ℝ^d; reason: the computation never uses the form of ∆_t
--   - reading: Σ_{s∈M_t} ‖∆_s‖² ‖X_s‖² in the third line → ‖v‖² (the page's ‖∆_t‖² of the last line); reason: the index s on ∆ is a typo; only the first and last members of the chain are stated
--   - encoding: ‖∆_t‖²_{V_t}, ‖∆_t‖²_{W_t} → the quadratic forms v'V_tv and v'W_tv; reason: equal for positive semidefinite matrices
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, proof of Theorem 1, p.26 (display after the event E_Δ)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Matrix
import Definitions.Def_DelayedGLCB_DUCB

namespace DelayedGLCB

open Matrix MostlyExplorationFree.GreedyBandit

/-- **`V_t` versus `W_t`: the missing samples add at most `G_t ‖v‖²`.**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, proof of Theorem 1, p.26:
"`‖∆_t‖²_{V_t} = ∆_t'V_t∆_t = ∆_t'(W_t + Σ_{s∈M_t} X_sX_s')∆_t = ∆_t'W_t∆_t + Σ_{s∈M_t} ∆_t'X_sX_s'∆_t
 ≤ ∆_t'W_t∆_t + Σ_{s∈M_t} ‖∆_s‖²‖X_s‖² ≤ ‖∆_t‖²_{W_t} + G_t‖∆_t‖²`."

For every outcome `ω` at which all feature vectors lie in the unit ball, every round `t` and every
`v ∈ ℝ^d`, along the run of DUCB-GLCB:
`v'V_t v = v'W_t v + Σ_{s∈M_t} (v'X_s)²` and `v'V_t v ≤ v'W_t v + G_t ‖v‖²`.

**Formalization Note.** The paper's vector is `∆_t = θ̂_t − θ*`; any `v` is allowed here. The page's
`‖∆_s‖²` in the third line is read as `‖∆_t‖²`, as in its last line. `M_t = missingSet`,
`G_t = missingCount`, `‖v‖ = l2norm v`. -/
theorem quad_V_le_quad_W {Ω : Type*} {d K : ℕ} (A : DUCB d K) (E : Env Ω d K) (ω : Ω)
    (hx : ∀ s a, l2norm (E.x s ω a) ≤ 1) (t : ℕ) (v : Fin d → ℝ) :
    (v ⬝ᵥ (V A E ω t *ᵥ v)
        = v ⬝ᵥ (W A E ω t *ᵥ v) + ∑ s ∈ missingSet E.D ω t, (v ⬝ᵥ X A E ω s) ^ 2) ∧
    v ⬝ᵥ (V A E ω t *ᵥ v)
      ≤ v ⬝ᵥ (W A E ω t *ᵥ v) + (missingCount E.D ω t : ℝ) * l2norm v ^ 2 := by sorry

end DelayedGLCB
