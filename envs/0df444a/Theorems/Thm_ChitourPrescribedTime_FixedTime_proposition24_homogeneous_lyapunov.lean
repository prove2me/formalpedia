-- Prove2me | Theorems.Thm_ChitourPrescribedTime_FixedTime_proposition24_homogeneous_lyapunov
-- name    : ChitourPrescribedTime.FixedTime.proposition24_homogeneous_lyapunov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:07:36.665838+00:00
-- url     : https://prove2.me/theorems/04b711ce-6943-49db-a8d9-2d2e9a5091ff
-- title:
--   Proposition 24 — uniform gains and a homogeneous $C^1$ Lyapunov function with $\dot V_\kappa\le -CV_\kappa^{1+\alpha(\kappa)}$
-- statement:
--   Let $n\ge1$. There exist gains $\ell_1,\dots,\ell_n>0$ and a constant $C>0$ such that, for every $\kappa\in[-\tfrac1{2n},\tfrac1{2n}]$:
--
--   1. $V_\kappa$ of (35) is $C^1$ on $\mathbb R^n$, nonnegative, and vanishes only at the origin;
--   2. along the closed loop $\dot x=J_nx+\omega^H_\kappa(x)e_n$,
--   $$\dot V_\kappa\le -C\,V_\kappa^{1+\alpha(\kappa)},\qquad \alpha(\kappa)=\frac{\kappa}{2+\kappa},$$
--   with the same $C$ for every $\kappa$ in the range;
--   3. $V_\kappa$ is $\mathbf r(\kappa)$-homogeneous of degree $2+\kappa$: $V_\kappa(D^{\mathbf r(\kappa)}_\mu x)=\mu^{2+\kappa}V_\kappa(x)$ for all $\mu>0$ and $x$;
--   4. the feedback $u=\omega^H_\kappa(x)$ globally asymptotically stabilizes the pure chain (31) at the origin.
--
--   This proposition supplies the gains and the constant $C$ used by Theorems 28 and 30, and shows that their hypothesis (36) can be met.
--
--   **Formalization Note** "Stabilizes the system (31)" is read as global asymptotic stability in the sense of Definition 1(b) with $\Omega=\mathbb R^n$, over all Carathéodory solutions. $C$ is quantified before $\kappa$ ("independent of $\kappa$"). The paper's index $j$ is `j.val + 1` for `j : Fin n`.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1034, Proposition 24, eqs. (35)–(36)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_FixedTime_Stability
import Definitions.Def_ChitourPrescribedTime_FixedTime_PureChain
import Definitions.Def_ChitourPrescribedTime_FixedTime_Feedback
import Definitions.Def_ChitourPrescribedTime_FixedTime_Lyapunov

namespace ChitourPrescribedTime.FixedTime

/-- Proposition 24 (p. 1034): there are gains `ℓ_j > 0` and one constant `C > 0` such that
for every `κ ∈ [-1/(2n), 1/(2n)]`: (36) holds, `V_κ` is `C¹` and positive definite, `V_κ` is
`r(κ)`-homogeneous of degree `2 + κ`, and `ω^H_κ` globally asymptotically stabilizes (31). -/
theorem proposition24_homogeneous_lyapunov (n : ℕ) (hn : 1 ≤ n) :
    ∃ ℓ : Fin n → ℝ, (∀ j, 0 < ℓ j) ∧ ∃ C : ℝ, 0 < C ∧ Decay36 ℓ C ∧
      ∀ κ ∈ Set.Icc (-(1 / (2 * (n : ℝ)))) (1 / (2 * (n : ℝ))),
        ContDiff ℝ 1 (lyapV ℓ κ) ∧
        (∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ lyapV ℓ κ x) ∧
        (∀ x : EuclideanSpace ℝ (Fin n), lyapV ℓ κ x = 0 ↔ x = 0) ∧
        (∀ μ : ℝ, 0 < μ → ∀ x : EuclideanSpace ℝ (Fin n),
          lyapV ℓ κ (dilK κ μ x) = μ ^ (2 + κ) * lyapV ℓ κ x) ∧
        GloballyAsymptoticallyStable (fun (_ : ℝ) (x : EuclideanSpace ℝ (Fin n)) =>
          chainField n x (omegaH ℓ κ x)) := by sorry

end ChitourPrescribedTime.FixedTime
