-- Prove2me | Theorems.Thm_AstromPOMDP_Reduction_kernel_grouping
-- name    : AstromPOMDP.Reduction.kernel_grouping
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:08:02.58655+00:00
-- url     : https://prove2.me/theorems/ba29fa0d-2de5-474b-b99c-43ba29dcfb8d
-- title:
--   §IV, proof of Theorem 3, p. 188 — (4.9) is identical to (3.28): the integral against (4.1) is Σ_j V(z^j/‖z^j‖)‖z^j‖
-- statement:
--   For every function $V$ on vectors, control $u$, time $t$ and vector $w$, the integral of $V$ against the transition probability $P(w,\cdot,u)$ of (4.1), which is concentrated on the finitely many points $z^k(u,w)/\|z^k(u,w)\|$, equals the second term of (3.28):
--   $$
--   \int V(y)\,P(w,dy,u)=\sum_{y'}P(w,\{y'\},u)\,V(y')=\sum_j V\Big(\frac{z^j(u,w)}{\|z^j(u,w)\|}\Big)\|z^j(u,w)\| ,
--   $$
--   the middle sum running over the distinct values $y'$ of $z^k(u,w)/\|z^k(u,w)\|$.
--
--   This is why the functional equation (4.9) of the completely observed problem P.2 is literally (3.28): outputs leading to the same next distribution merge into one atom of the kernel.
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), DOI 10.1016/0022-247X(65)90154-X, p. 188, §IV, proof of Theorem 3, (4.8)–(4.9)

import Mathlib
import Definitions.Def_AstromPOMDP_Reduction_BeliefProcess

namespace AstromPOMDP.Reduction

open Classical in
/-- Åström (1965), J. Math. Anal. Appl. 10:174–205, §IV, proof of Theorem 3, (4.8)–(4.9), p. 188:
"The equation (4.1) now implies that Eq. (4.9) is identical to (3.28)." For every function `V`
(standing for `V_{t+1}`), control `u`, time `t` and vector `w`, the integral
`∫ V(y) P(w, dy, u)` of `V` against the finite-support transition probability (4.1) — the sum over
the distinct values `y'` of `z^k(u, w)/‖z^k(u, w)‖` of `P(w, {y'}, u) V(y')` — equals
`Σ_j V(z^j(u, w)/‖z^j(u, w)‖) ‖z^j(u, w)‖`, the second term of (3.28). -/
theorem kernel_grouping {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (V : (St → ℝ) → ℝ) (u : Fin r → ℝ) (t : ℕ) (w : St → ℝ) :
    ∑ y ∈ Finset.univ.image (fun j => bayesNext M u t w j), kernelProb M u t w {y} * V y =
      ∑ j, V (bayesNext M u t w j) * l1 (zvec M u t w j) := by sorry

end AstromPOMDP.Reduction
