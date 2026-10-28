-- Prove2me | Theorems.Thm_CoherenceTracking_Dephasing_bloch_parametrization
-- name    : CoherenceTracking.Dephasing.bloch_parametrization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T02:30:18.825814+00:00
-- url     : https://prove2.me/theorems/21e0daec-da05-4cf2-aca6-c5fc02989162
-- title:
--   §II.B, eqs. (7)–(11), p. 3 — Bloch parametrization of qubit states, and coherence as |ρ₀₁|²
-- statement:
--   Let $\rho$ be a qubit density matrix: a complex $2\times2$ matrix with $\operatorname{Tr}\rho=1$, $\rho_{10}=\rho_{01}^*$ and $\operatorname{Tr}(\rho^2)\le1$. Write $v_\alpha=\operatorname{Re}\operatorname{Tr}(\rho\sigma_\alpha)$ for $\alpha\in\{x,y,z\}$, and $c=v_x^2+v_y^2$ for its coherence. Then:
--
--   1. $\rho$ is recovered from its Bloch vector, and the coherence measures the off-diagonal entry:
--   $$\rho=\tfrac12\bigl(I+\vec v\cdot\vec\sigma\bigr),\qquad c=4\,|\rho_{01}|^2 .$$
--   2. For every real vector $\vec v\in\mathbb R^3$, the Bloch vector of $\tfrac12(I+\vec v\cdot\vec\sigma)$ is $\vec v$.
--   3. The matrix $\tfrac12(I+\vec v\cdot\vec\sigma)$ is a qubit state if and only if $v_x^2+v_y^2+v_z^2\le 1$.
--
--   This is the dictionary between density matrices and Bloch vectors (the Bloch ball) on which the rest of the mission rests; item 1 also says that the coherence $c$ is, up to the factor $4$, the squared modulus of the off-diagonal element of $\rho$.
--
--   **Formalization Note** The paper's eq. (8) prints $v_\alpha=\tfrac12\operatorname{Tr}(\rho\sigma_\alpha)$, which is inconsistent with its eq. (9); the statement follows (9). Items 2 and 3 hold for every real $\vec v$, not only for Bloch vectors of states.
-- source:
--   Lidar & Schneider, Stabilizing qubit coherence via tracking-control, arXiv:quant-ph/0410048v1, p. 3, §II.B, eqs. (7), (9), (11)

import Mathlib
import Definitions.Def_CoherenceTracking_Dephasing_Model

namespace CoherenceTracking.Dephasing
theorem bloch_parametrization :
    (∀ ρ : Qmat, IsQubitState ρ →
        blochState (blochVec ρ) = ρ ∧ coherence ρ = 4 * Complex.normSq (ρ 0 1)) ∧
    (∀ v : BVec, blochVec (blochState v) = v) ∧
    (∀ v : BVec, IsQubitState (blochState v) ↔ ∑ α, v α ^ 2 ≤ 1) := by sorry
end CoherenceTracking.Dephasing
