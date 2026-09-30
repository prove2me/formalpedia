-- Prove2me | Theorems.Thm_ChitourPrescribedTime_Linear_proposition13_scaled_lmi
-- name    : ChitourPrescribedTime.Linear.proposition13_scaled_lmi
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:02:31.438975+00:00
-- url     : https://prove2.me/theorems/6915693b-8584-4f2a-a807-3c7b23ee1a01
-- title:
--   Proposition 13 — the $\eta$-scaled LMI (20) with $S_\eta=D^{\mathbf r}_\eta S D^{\mathbf r}_\eta$, $K_\eta=D^{\mathbf r}_\eta K$
-- statement:
--   Let $n\ge1$ and $\underline b>0$. There exist a constant $\rho>0$, a real symmetric positive definite $n\times n$ matrix $S$ and a vector $K\in\mathbb R^n$ such that for every $C>0$ there is $\eta_1>0$ for which, with
--   $$S_\eta = D^{\mathbf r}_\eta\, S\, D^{\mathbf r}_\eta, \qquad K_\eta = D^{\mathbf r}_\eta K,$$
--   the inequality
--   $$\big(a D_{\mathbf r} + J_n - b\, e_n K_\eta^T\big)^T S_\eta + S_\eta\big(a D_{\mathbf r} + J_n - b\, e_n K_\eta^T\big) \preceq -\rho\,\eta\,\big(D^{\mathbf r}_\eta\big)^2$$
--   holds for all $a\in[-C,C]$, $\eta\ge\eta_1$ and $b\ge\underline b$ ($\preceq$ is the Loewner order).
--
--   This is the LMI form of the argument behind Proposition 12: the feedback parameter $\eta$ appears explicitly as a factor in the decay rate.
--
--   **Formalization Note** The page writes the right-hand side as $-\mu_*\eta(D^{\mathbf r})^2_\eta$ and never defines $\mu_*$. The page's argument (multiply (16) on both sides by $D^{\mathbf r}_\eta$) gives it as the positive constant of the LMI, so the statement uses the $\rho$ introduced in its first line. $(D^{\mathbf r})^2_\eta$ is read as $(D^{\mathbf r}_\eta)^2$. The requirement $\eta_1>0$ is added: for $\eta\le 0$ the dilation $D^{\mathbf r}_\eta$ is not the paper's object. The hypothesis $n\ge1$ is the standing assumption of §3.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), p. 1029, Proposition 13, eq. (20)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_Linear_chain

namespace ChitourPrescribedTime.Linear

open Matrix
open scoped MatrixOrder

/-- Proposition 13 (p. 1029), with the page's undefined `µ_*` read as the `ρ` of its first line:
there are `ρ > 0`, a real symmetric positive definite `S` and `K ∈ ℝ^n` such that for every
`C > 0` there is `η₁ > 0` with, writing `S_η = D^r_η S D^r_η` and `K_η = D^r_η K`,
`(a D_r + J_n - b e_n K_ηᵀ)ᵀ S_η + S_η (a D_r + J_n - b e_n K_ηᵀ) ≤ -ρ η (D^r_η)²`
for all `a ∈ [-C, C]`, `η ≥ η₁` and `b ≥ b̲`. -/
theorem proposition13_scaled_lmi (n : ℕ) (hn : 1 ≤ n) (bmin : ℝ) (hbmin : 0 < bmin) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ S : Matrix (Fin n) (Fin n) ℝ, S.PosDef ∧ ∃ K : Fin n → ℝ,
      ∀ C : ℝ, 0 < C → ∃ η1 : ℝ, 0 < η1 ∧
        ∀ a : ℝ, a ∈ Set.Icc (-C) C → ∀ η : ℝ, η1 ≤ η → ∀ b : ℝ, bmin ≤ b →
          (a • Dr n + jordanBlock n - b • vecMulVec (eN n) (dil n η *ᵥ K))ᵀ *
                (dil n η * S * dil n η) +
              (dil n η * S * dil n η) *
                (a • Dr n + jordanBlock n - b • vecMulVec (eN n) (dil n η *ᵥ K))
            ≤ -((ρ * η) • (dil n η * dil n η)) := by sorry

end ChitourPrescribedTime.Linear
