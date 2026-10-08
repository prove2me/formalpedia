-- Prove2me | Theorems.Thm_DataDrivenRO_Discrete_theorem_EC_1
-- name    : DataDrivenRO.Discrete.theorem_EC_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:43:47.480241+00:00
-- url     : https://prove2.me/theorems/8df5a5f9-993c-4585-9cde-6e642e155aaf
-- title:
--   Theorem EC.1 — the CVaR set has support function equal to CVaR
-- statement:
--   Let $P_p$ be a law on the listed vectors $a_0,\ldots,a_{n-1}\in\mathbb R^d$, with $p\in\Delta_n$. For $0<\epsilon<1$, define $U^{\operatorname{CVaR}_{P_p}}_\epsilon$ by reweighting those vectors with $q\in\Delta_n$ and $q_j\le p_j/\epsilon$. Then for every direction $v$,
--
--   $$
--   \delta^*(v\mid U^{\operatorname{CVaR}_{P_p}}_\epsilon)
--     =\operatorname{CVaR}^{P_p}_{\epsilon}(v).
--   $$
--
--   This identity links a risk functional to the support function of a finite-dimensional uncertainty set and is the central cited result in the proof of Theorem 4.
--
--   **Formalization Note** The source's final CVaR expression omits the $\epsilon$ subscript typographically; the set and the surrounding section fix that level. The real support function is evaluated on a nonempty compact reweighting set under these hypotheses.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem EC.1 and (EC.1), p. ec2

import Mathlib
import Definitions.Def_DataDrivenRO_Discrete_Setting

namespace DataDrivenRO.Discrete

/-- The finite-support CVaR set has support function equal to CVaR.  Theorem EC.1,
p. ec2, quoted from Rockafellar and Uryasev. -/
theorem theorem_EC_1 {d n : ℕ} (a : Fin n → (Fin d → ℝ)) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : Fin d → ℝ) :
    RobustMDP.Shared.supportFunction (cvarSet a p ε) v = CVaR a p ε v := by sorry

end DataDrivenRO.Discrete
