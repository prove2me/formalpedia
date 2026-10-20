-- Prove2me | Theorems.Thm_DynkinAsymInfo_Linear_theorem_6_10
-- name    : DynkinAsymInfo.Linear.theorem_6_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:18:47.859843+00:00
-- url     : https://prove2.me/theorems/6bece947-b678-4242-8c62-7eb0e8b8210f
-- title:
--   Theorem 6.10 — threshold and reflecting stops form a saddle point
-- statement:
--   Assume $\mu_0<0<\mu_1$, $\sigma>0$, $\varepsilon>0$, and initial state $x>0$ and odds $\phi>0$. Let $A<B$ be the explicit thresholds of (90) and (93), let $V_1,V$ be the piecewise power-function values of (89), (91), (94)–(97), and put $V_0(\phi)=V(\phi)-\phi V_1(\phi)$. Player 1 stops when the reflected odds $\Phi^B$ first reach $A$. Player 2 does not stop in type zero and uses the reflecting randomised control $\Gamma^B$ in type one. This strategy pair is a saddle point of the ex-ante game with $f(y)=y$ and $g(y)=(1+\varepsilon)y$. Its payoffs are
--   $$\widehat J_{x,\phi}(\tau_A,(0,\Gamma^B))=xV(\phi),\quad J^0_{x,\phi}(\tau_A,0)=xV_0(\phi),\quad J^1_{x,\phi}(\tau_A,\Gamma^B)=xV_1(\phi).$$
--   The saddle inequalities hold against every admissible observation stopping time and every informed randomised stopping strategy. These are the explicit equilibrium and value claims of the paper.
--
--   **Formalization Note.** $\pi=\phi/(1+\phi)$; the value identity concerns the scaled payoff $\widehat J=(1+\phi)J$. The threshold, control and values are defined closed forms, not additional hypotheses. An initial jump of $\Gamma^B$ is permitted and counted.
-- source:
--   De Angelis, Ekström, Glover, Dynkin Games with Incomplete and Asymmetric Information, arXiv:1810.07674v5, p. 24, Theorem 6.10

import Mathlib
import Definitions.Def_DynkinAsymInfo_Linear_ClosedForms

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DynkinAsymInfo.Linear
set_option autoImplicit false

/-- De Angelis, Ekström, Glover, *Dynkin Games with Incomplete and Asymmetric Information*,
arXiv:1810.07674v5, p. 24, Theorem 6.10. The candidate threshold time and reflected
randomisation control form a saddle point, and their three payoffs equal the explicit values.

**Formalization Note.** The GBM is given by its explicit strong solution. The type is
`1{Theta < π}`. The two strategy classes use the augmented filtrations of X and (X,θ),
never U. Stopping times take values in `WithTop ℝ≥0`, and nonnegative extended integrals
avoid a junk value for nonintegrable payoffs. The Stieltjes integral in `J0` and `J1`
includes the jump at zero. `π=ϕ/(1+ϕ)`, so only strictly positive x and ϕ are used.
The boundaries and values are the definitions from (89)–(97), not theorem hypotheses. -/
theorem theorem_6_10 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (h62 : p.mu0 < 0 ∧ 0 < p.mu1) (eps : ℝ) (heps : 0 < eps)
    (x phi : ℝ) (hx : 0 < x) (hphi : 0 < phi) :
    let pi := phi / (1 + phi)
    let A := Ab p eps
    let B := Bb p eps
    IsSaddle p st x pi (fun y => y) (fun y => (1 + eps) * y)
      (tauA p st x pi A B) (GammaStar p st x pi B) ∧
    Jhat p st x pi (fun y => y) (fun y => (1 + eps) * y)
      (tauA p st x pi A B) (GammaStar p st x pi B) =
        ENNReal.ofReal (x * V p eps phi) ∧
    J0 p st x pi (fun y => y) (fun y => (1 + eps) * y)
      (tauA p st x pi A B) (fun _ _ => 0) =
        ENNReal.ofReal (x * V0 p eps phi) ∧
    J1 p st x pi (fun y => y) (fun y => (1 + eps) * y)
      (tauA p st x pi A B) (GammaB p st x pi B) =
        ENNReal.ofReal (x * V1 p eps phi) := by sorry

end DynkinAsymInfo.Linear
