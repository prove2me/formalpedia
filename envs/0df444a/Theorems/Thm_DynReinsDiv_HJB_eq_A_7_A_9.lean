-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_eq_A_7_A_9
-- name    : DynReinsDiv.HJB.eq_A_7_A_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:34:29.409847+00:00
-- url     : https://prove2.me/theorems/0ff3a55e-af25-4570-be97-c4d85fbfe22e
-- title:
--   (A.7)–(A.9) — A and B are non-increasing and Lipschitz, 0 < A ≤ ½min{y⁻², μ₂}, 0 < B ≤ min{y⁻¹, μ₁}, and their derivatives
-- statement:
--   Let $A$, $B$ be the functions (A.5), (A.6) of a model satisfying the tail assumption (3.3) and $0<\gamma<\mu_1$, and let $F$ be the claim distribution function. Then:
--   1. $A$ and $B$ are non-increasing and Lipschitz continuous on $\mathbb R$;
--   2. for every $y>0$ (A.7),
--   $$0<A(y)\le\tfrac12\min\{y^{-2},\mu_2\},\qquad 0<B(y)\le\min\{y^{-1},\mu_1\};$$
--   3. for every $y>0$ such that $F$ is continuous at $y^{-1}$ (A.8),
--   $$y^3A'(y)=y^2B'(y)=F(y^{-1})-1\le0;$$
--   4. for every $y<0$ (A.9), $A'(y)=B'(y)=0$.
--
--   These facts make the reduction (A.10) of $\mathcal L$ and the derivative formula (A.13) for $f$ possible, and give the bounds on the coefficients of the penalized equation.
--
--   **Formalization Note** The paper's "for a.e. $y>0$" in (A.8) is posed at every $y>0$ at which $F$ is continuous at $y^{-1}$; $F$ has at most countably many discontinuities, so this implies the almost-everywhere statement. "Decreasing" is read as non-increasing ($A$, $B$ are constant on $y\le0$). Positivity of $A$, $B$ uses that the claims are not almost surely $0$, which follows from $\mu_1>\gamma>0$.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 22, (A.7)–(A.9)

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model

namespace DynReinsDiv.HJB

theorem eq_A_7_A_9 (M : Model) :
    Antitone M.A ∧ Antitone M.B ∧
    (∃ K : NNReal, LipschitzWith K M.A) ∧ (∃ K : NNReal, LipschitzWith K M.B) ∧
    (∀ y : ℝ, 0 < y →
      0 < M.A y ∧ M.A y ≤ 1 / 2 * min (y ^ 2)⁻¹ M.μ₂ ∧
      0 < M.B y ∧ M.B y ≤ min y⁻¹ M.μ₁) ∧
    (∀ y : ℝ, 0 < y → ContinuousAt M.F y⁻¹ →
      HasDerivAt M.A ((M.F y⁻¹ - 1) / y ^ 3) y ∧
      HasDerivAt M.B ((M.F y⁻¹ - 1) / y ^ 2) y ∧
      M.F y⁻¹ - 1 ≤ 0) ∧
    (∀ y : ℝ, y < 0 → HasDerivAt M.A 0 y ∧ HasDerivAt M.B 0 y) := by sorry

end DynReinsDiv.HJB
