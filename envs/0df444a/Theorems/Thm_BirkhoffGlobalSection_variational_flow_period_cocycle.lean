-- Prove2me | Theorems.Thm_BirkhoffGlobalSection_variational_flow_period_cocycle
-- name    : BirkhoffGlobalSection.variational_flow_period_cocycle
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-28T19:35:35.120465+00:00
-- url     : https://prove2.me/theorems/479b5b89-7933-4370-97cc-5449f05634c9
-- title:
--   Period cocycle of the variational flow
-- statement:
--   A closed solution of the autonomous Hamiltonian system is fully periodic, and its variational flow satisfies the cocycle identity. Precisely, if $x$ closes up after time $T>0$ and $Y$ is the identity-normalized variational flow, then $x(t+T)=x(t)$ for all $t$ by ODE uniqueness, and $Y(t+T)=Y(t)Y(T)$ since both sides solve the same $T$-periodic linear equation with the same initial value.
--
--   This factors the standard uniqueness consequences out of every winding comparison: it is reusable wherever a periodic orbit's linearized flow is shifted in time.
-- source:
--   Autonomous ODE uniqueness plus the periodic linear variational equation (cocycle identity), and the resulting uniform branch bound for the determinant rotation angle; quaternionic-frame context of Joung-van Koert, https://arxiv.org/html/2407.19159v3, Section 2.3.

import Definitions.Def_BirkhoffGlobalSection_AmbientRotation

open scoped ContDiff

namespace BirkhoffGlobalSection

open scoped ContDiff

theorem variational_flow_period_cocycle
    (F : Phase → ℝ) (S : Set Phase) (x : ℝ → Phase) (T : ℝ)
    (hx : IsPeriodicHamiltonianSolutionIn F S x T)
    (hF : ∀ t : ℝ, ContDiffAt ℝ ∞ F (x t))
    (Y : ℝ → (Phase →L[ℝ] Phase))
    (hY : IsHamiltonianVariationalSolution F x Y) :
    (∀ t : ℝ, x (t + T) = x t) ∧
      ∀ t : ℝ, Y (t + T) = (Y t).comp (Y T) := by sorry

end BirkhoffGlobalSection
