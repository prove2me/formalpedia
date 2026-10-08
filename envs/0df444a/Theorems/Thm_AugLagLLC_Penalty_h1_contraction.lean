-- Prove2me | Theorems.Thm_AugLagLLC_Penalty_h1_contraction
-- name    : AugLagLLC.Penalty.h1_contraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:20.851396+00:00
-- url     : https://prove2.me/theorems/e40884af-fc06-4080-8902-dfa74ad8dbb1
-- title:
--   Proof of Theorem 5.4, p. 13 — if ρₖ → ∞ then ‖h₁(xₖ)‖∞ ≤ (3LM²/ρₖ)‖h₁(xₖ₋₁)‖∞ for k large
-- statement:
--   Assume the hypotheses of Theorem 5.4 for problem (5.1) (as in (5.10)) and suppose that $\rho_k\to\infty$. Then there is a constant $C>0$ such that
--   $$\|h_1(x_k)\|_\infty\le\frac{C}{\rho_k}\,\|h_1(x_{k-1})\|_\infty\quad\text{for } k \text{ large enough}.$$
--
--   On the page $C=3LM^2$. Since $\rho_k\to\infty$, the factor $C/\rho_k$ eventually drops below $\tau$, so the test of Step 4 passes and the penalty parameter stops growing, which contradicts $\rho_k\to\infty$ and proves Theorem 5.4.
--
--   **Formalization Note** The constants $L$, $M$ are existential in the proof, so $C$ is existential. The intermediate bound $\|\lambda_k-\lambda_*\|_\infty\le3M\|h_1(x_{k-1})\|_\infty$ of the page is part of this item's proof and not posed separately. The hypothesis $0<\tau$ of the goal theorem is not needed here and is not assumed.
-- source:
--   Andreani, Birgin, Martínez & Schuverdt, On augmented Lagrangian methods with general lower-level constraints, HAL hal-01295437v1, p. 13, proof of Theorem 5.4, the inequality after (5.11)

import Mathlib
import Definitions.Def_AugLagLLC_Penalty_SecondOrder

open Filter
open scoped Topology

namespace AugLagLLC.Penalty

/-- Proof of Theorem 5.4, p. 13: under the hypotheses of Theorem 5.4 and the contradiction
hypothesis `ρₖ → ∞`, there is `C > 0` (the page's `3LM²`) with
`‖h₁(xₖ)‖∞ ≤ (C / ρₖ) ‖h₁(xₖ₋₁)‖∞` for `k` large. -/
theorem h1_contraction
    {n m1 m2 : ℕ} (P : Problem n m1 0 m2 0) (hP : P.IsC1)
    {τ γ ρ1 : ℝ} {lamMin lamMax : Fin m1 → ℝ} {muMax : Fin 0 → ℝ} {ε : ℕ → ℝ}
    (hpar : Problem.IsParams τ γ ρ1 lamMin lamMax muMax ε)
    {x : ℕ → EuclideanSpace ℝ (Fin n)} {ρ : ℕ → ℝ} {lamBar : ℕ → Fin m1 → ℝ}
    {muBar : ℕ → Fin 0 → ℝ} {v : ℕ → Fin m2 → ℝ} {u : ℕ → Fin 0 → ℝ}
    -- Assumption 1: a run of Algorithm 3.1 on (5.1), with the safeguard Definition of §5.1
    (hrun : P.IsProjRun τ γ ρ1 lamMin lamMax muMax ε x ρ lamBar muBar v u)
    {xs : EuclideanSpace ℝ (Fin n)} (hlim : Tendsto x atTop (𝓝 xs))
    -- Assumption 2
    (hfeas : xs ∈ P.Omega1 ∩ P.Omega2)
    -- Assumption 3
    (hLI : LinearIndependent ℝ
      (Sum.elim (fun i => gradient (P.h1 i) xs) (fun i => gradient (P.h2 i) xs)))
    -- Assumption 4
    (hC2 : P.IsC2At xs)
    -- Assumption 5
    (lamS : Fin m1 → ℝ) (vS : Fin m2 → ℝ) (hSOSC : P.SOSC0 lamS vS xs)
    -- Assumption 6
    (hbox : ∀ i, lamMin i < lamS i ∧ lamS i < lamMax i)
    (η : ℕ → ℝ) (hη : Tendsto η atTop (𝓝 0))
    (hεη : ∀ k, 1 ≤ k → ε k ≤ η k * ‖P.h1vec (x k)‖)
    -- the contradiction hypothesis of the proof
    (hρ : Tendsto ρ atTop atTop) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k in atTop,
      ‖P.h1vec (x k)‖ ≤ C / ρ k * ‖P.h1vec (x (k - 1))‖ := by sorry

end AugLagLLC.Penalty
