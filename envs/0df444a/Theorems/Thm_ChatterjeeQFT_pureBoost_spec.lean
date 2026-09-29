-- Prove2me | Theorems.Thm_ChatterjeeQFT_pureBoost_spec
-- name    : ChatterjeeQFT.pureBoost_spec
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T21:40:41.892422+00:00
-- url     : https://prove2.me/theorems/d7109e6a-197c-48aa-9ad2-0340101f6727
-- title:
--   Existence and uniqueness of the positive-definite boost $V_p$ with $\kappa(V_p)p^* = p$
-- statement:
--   Fix $m > 0$ and let $p^* = (m,0,0,0)$. For every $p \in X_m$ there is exactly one
--   positive-definite $V \in SL(2,\mathbb{C})$ with $\kappa(V)p^* = p$, and it is given by the closed
--   formula
--
--   $$V_p \;=\; \frac{M(p)/m + I}{\sqrt{2 + 2p^0/m}} ,$$
--
--   i.e. the positive-definite square root of $M(p)/m$. Concretely the statement asserts four things
--   about this explicit matrix: $\det V_p = 1$; $V_p$ is positive definite; $\kappa(V_p)p^* = p$; and
--   any $V$ with those three properties equals $V_p$. In the physics literature $\kappa(V_p)$ is the
--   "pure boost" taking $p^*$ to $p$; the uniqueness is what makes the electron inner product of
--   §25.3 well defined.
-- source:
--   S. Chatterjee, *Lectures on Quantum Field Theory* (Stanford, 2018-19, combined scribed lecture notes), https://souravchatterjee.su.domains/qft-lectures-combined.pdf, Lecture 25 §25.3, p. 108 ("for any $p \in X_m$ there exists a unique positive-definite $V_p \in SL(2,\mathbb{C})$ such that $\kappa(V_p)(p^*) = p$").

import Mathlib
import Definitions.Def_ChatterjeeQFT_MassShell
import Definitions.Def_ChatterjeeQFT_SL2C
open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

namespace ChatterjeeQFT

theorem pureBoost_spec (m : ℝ) (hm : 0 < m) (p : Fin 4 → ℝ) (hp : p ∈ massShell m) :
    (pureBoost m p).det = 1 ∧ (pureBoost m p).PosDef ∧
      kappa (pureBoost m p) (restMomentum m) = p ∧
      ∀ V : Matrix (Fin 2) (Fin 2) ℂ, V.det = 1 → V.PosDef →
        kappa V (restMomentum m) = p → V = pureBoost m p := by sorry

end ChatterjeeQFT
