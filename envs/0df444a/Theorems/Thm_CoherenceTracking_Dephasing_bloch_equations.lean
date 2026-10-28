-- Prove2me | Theorems.Thm_CoherenceTracking_Dephasing_bloch_equations
-- name    : CoherenceTracking.Dephasing.bloch_equations
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:27.752767+00:00
-- url     : https://prove2.me/theorems/7f6e3fe7-a8c3-418a-b4ea-c028f975b6b2
-- title:
--   §III.B, eqs. (30)–(32), p. 5 — the controlled dephasing master equation is equivalent to the Bloch equations
-- statement:
--   Fix $\hbar>0$ and a dephasing rate $\gamma\in\mathbb R$. For controls $\omega=(\omega_0,\omega_1,\omega_2)$ let $H=\tfrac{\hbar}{2}(\omega_0\sigma_z+\omega_1\sigma_x-\omega_2\sigma_y)$, let
--   $$\mathcal L_\omega(\rho)=-\frac{i}{\hbar}[H,\rho]+\frac{\gamma}{2}(\sigma_z\rho\sigma_z-\rho)$$
--   be the right-hand side of the master equation (32), and let
--   $$M_\omega=\begin{pmatrix}-\gamma&-\omega_0&-\omega_2\\ \omega_0&-\gamma&-\omega_1\\ \omega_2&\omega_1&0\end{pmatrix}$$
--   be the matrix of the Bloch equations (30). Write $\vec v(\rho)$ for the Bloch vector $v_\alpha=\operatorname{Re}\operatorname{Tr}(\rho\sigma_\alpha)$. Then:
--
--   1. For every complex $2\times2$ matrix $\rho$ and every $\omega$, $\ \vec v(\mathcal L_\omega(\rho))=M_\omega\,\vec v(\rho)$.
--   2. If a matrix trajectory $\rho(t)$ solves (32) on $[0,T)$ with time-dependent controls $\omega(t)$, then its Bloch vector $\vec v(\rho(t))$ solves (30) on $[0,T)$.
--   3. Conversely, if $\vec v(t)$ solves (30) on $[0,T)$, then $\rho(t)=\tfrac12(I+\vec v(t)\cdot\vec\sigma)$ solves (32) on $[0,T)$.
--
--   Here "solves on $[0,T)$" means continuous on $[0,T)$ and differentiable with the prescribed derivative at every $t\in(0,T)$. This is the reduction of the density-matrix problem to a linear system for the Bloch vector, used by every later step.
--
--   **Formalization Note** The controls are arbitrary real functions of time. The page introduces (32) under the heading "uncontrolled (free) dynamics: $H=0$", but (32) carries the Hamiltonian, and its equivalence with the controlled system (30) is the reading the paper uses.
-- source:
--   Lidar & Schneider, Stabilizing qubit coherence via tracking-control, arXiv:quant-ph/0410048v1, p. 5, §III.B, eqs. (30)–(32), with H of eq. (13), p. 3

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
theorem bloch_equations (hbar γ : ℝ) (hhbar : 0 < hbar) :
    (∀ (ω : Fin 3 → ℝ) (ρ : Qmat),
        blochVec (masterRHS hbar γ ω ρ) = (blochMatrix γ ω).mulVec (blochVec ρ)) ∧
    (∀ (ω : ℝ → Fin 3 → ℝ) (ρ : ℝ → Qmat) (T : ℝ),
        SolvesMaster hbar γ ω ρ T → SolvesBloch γ ω (fun t => blochVec (ρ t)) T) ∧
    (∀ (ω : ℝ → Fin 3 → ℝ) (v : ℝ → BVec) (T : ℝ),
        SolvesBloch γ ω v T → SolvesMaster hbar γ ω (fun t => blochState (v t)) T) := by sorry
end CoherenceTracking.Dephasing
