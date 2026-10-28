-- Prove2me | Theorems.Thm_CoherenceTracking_Dephasing_coherence_tracking_breakdown
-- name    : CoherenceTracking.Dephasing.coherence_tracking_breakdown
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:33.574259+00:00
-- url     : https://prove2.me/theorems/c9418be8-4f2c-4a2b-8aad-c129ea4054df
-- title:
--   §III.B.2, eqs. (36)–(42), p. 6 — under pure dephasing, coherence can be held constant exactly on [0, t_b), t_b = v_z(0)²/(2γc), by fields that diverge at t_b
-- statement:
--   Consider a qubit with density matrix $\rho$ evolving under the master equation
--   $$\frac{\partial\rho}{\partial t}=-\frac{i}{\hbar}[H(t),\rho]+\frac{\gamma}{2}(\sigma_z\rho\sigma_z-\rho),\qquad H(t)=\frac{\hbar}{2}\bigl(\omega_0(t)\sigma_z+\omega_1(t)\sigma_x-\omega_2(t)\sigma_y\bigr),$$
--   with $\hbar>0$ and dephasing rate $\gamma>0$. Let $\rho_0$ be a qubit state with Bloch vector $\vec v(0)=(v_x(0),v_y(0),v_z(0))$, $v_\alpha=\operatorname{Tr}(\rho\sigma_\alpha)$, and coherence $c=v_x(0)^2+v_y(0)^2>0$. Let
--   $$t_b=\frac{v_z(0)^2}{2\gamma c}.$$
--   Then:
--
--   1. **(No-go.)** For every choice of controls $\omega_0,\omega_1,\omega_2$ and every solution $\rho(t)$ on $[0,T)$ with $\rho(0)=\rho_0$ whose coherence stays equal to $c$, one has $v_z(t)^2=v_z(0)^2-2\gamma c\,t$ for all $t\in[0,T)$, and $T\le t_b$.
--   2. **(Achievability.)** If $v_z(0)\neq0$, then for every function $\omega_0$ the state $\rho(t)=\tfrac12(I+\vec v(t)\cdot\vec\sigma)$ with $\vec v(t)=(v_x(0),v_y(0),\operatorname{sign}(v_z(0))\sqrt{v_z(0)^2-2\gamma ct})$ starts at $\rho_0$, is a qubit state for every $t\in[0,t_b)$, keeps $v_x$, $v_y$ and hence the coherence $c$ fixed, and solves the master equation at every $t\in[0,t_b)$ with the fields $\omega_1,\omega_2$ of eqs. (41)–(42).
--   3. **(Divergence.)** If $v_z(0)\neq0$, then for every $\omega_0$ the fields of (41)–(42) satisfy $\omega_1(t)^2+\omega_2(t)^2\to+\infty$ as $t\to t_b^-$.
--
--   This is the main result of the paper: "At the breakdown time $t_b$ the control fields diverge … Thus, decay of the coherence can be prevented for $t<t_b$", and not beyond. If $v_z(0)=0$, then $t_b=0$, and item 1 says that the coherence cannot be held on any interval of positive length.
--
--   **Formalization Note** $\gamma>0$ and $c>0$ are added because $t_b$ divides by $2\gamma c$. A solution on $[0,T)$ is continuous on $[0,T)$ and satisfies the master equation at every $t\in(0,T)$; the controls are arbitrary real functions, and item 1 does not assume $v_x$, $v_y$ frozen. The sign $(\pm)$ of (37) is $\operatorname{sign}v_z(0)$. The Bloch vector is $v_\alpha=\operatorname{Re}\operatorname{Tr}(\rho\sigma_\alpha)$, following eq. (9) rather than the misprinted factor $\tfrac12$ of eq. (8).
-- source:
--   Lidar & Schneider, Stabilizing qubit coherence via tracking-control, arXiv:quant-ph/0410048v1, p. 6, §III.B.2, eqs. (36)–(42) and the sentence 'At the breakdown time t_b the control fields diverge'; abstract, p. 1

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
theorem coherence_tracking_breakdown (hbar γ : ℝ) (hhbar : 0 < hbar) (hγ : 0 < γ)
    (ρ0 : Qmat) (hρ0 : IsQubitState ρ0) (hc : 0 < coherence ρ0) :
    -- (i) no-go, (36)–(38): any controls, any constant-coherence solution of (32)
    (∀ (T : ℝ) (ω : ℝ → Fin 3 → ℝ) (ρ : ℝ → Qmat),
        ρ 0 = ρ0 → SolvesMaster hbar γ ω ρ T →
        (∀ t ∈ Set.Ico 0 T, coherence (ρ t) = coherence ρ0) →
        (∀ t ∈ Set.Ico 0 T,
            blochVec (ρ t) 2 ^ 2 = blochVec ρ0 2 ^ 2 - 2 * γ * coherence ρ0 * t) ∧
        T ≤ breakdownTime γ (blochVec ρ0)) ∧
    -- (ii) achievability, (37), (41)–(42): the tracked state solves (32) and keeps c on [0, t_b)
    (blochVec ρ0 2 ≠ 0 → ∀ ω0 : ℝ → ℝ,
        trackedState γ (blochVec ρ0) 0 = ρ0 ∧
        ∀ t ∈ Set.Ico 0 (breakdownTime γ (blochVec ρ0)),
          IsQubitState (trackedState γ (blochVec ρ0) t) ∧
          coherence (trackedState γ (blochVec ρ0) t) = coherence ρ0 ∧
          blochVec (trackedState γ (blochVec ρ0) t) 0 = blochVec ρ0 0 ∧
          blochVec (trackedState γ (blochVec ρ0) t) 1 = blochVec ρ0 1 ∧
          HasDerivAt (trackedState γ (blochVec ρ0))
            (masterRHS hbar γ (trackingFields γ (blochVec ρ0) ω0 t)
              (trackedState γ (blochVec ρ0) t)) t) ∧
    -- (iii) divergence of the control fields at t_b
    (blochVec ρ0 2 ≠ 0 → ∀ ω0 : ℝ → ℝ,
        Filter.Tendsto
          (fun t => trackingFields γ (blochVec ρ0) ω0 t 1 ^ 2 +
            trackingFields γ (blochVec ρ0) ω0 t 2 ^ 2)
          (nhdsWithin (breakdownTime γ (blochVec ρ0)) (Set.Iio (breakdownTime γ (blochVec ρ0))))
          Filter.atTop) := by sorry
end CoherenceTracking.Dephasing
