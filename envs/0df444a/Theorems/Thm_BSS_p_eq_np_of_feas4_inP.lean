-- Prove2me | Theorems.Thm_BSS_p_eq_np_of_feas4_inP
-- name    : BSS.p_eq_np_of_feas4_inP
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T15:38:43.483277+00:00
-- url     : https://prove2.me/theorems/7551c563-9233-47b7-9b4f-52492e6c7589
-- title:
--   §6 Corollary: a polynomial time feasibility algorithm gives $P = NP$ over $\mathbb{R}$
-- statement:
--   The Corollary of §6 (p. 27): any algorithm for the feasibility problem can be used to solve any
--   problem in $NP$ over $\mathbb{R}$, and if that algorithm runs in polynomial time then every
--   problem in $NP$ over $\mathbb{R}$ can be solved in polynomial time.
--
--   Formally: if 4-Feasibility is in $P$ over $\mathbb{R}$, then every decision problem in $NP$ over
--   $\mathbb{R}$ is in $P$. This follows from the Main Theorem by composing the reduction with the
--   assumed polynomial time decision procedure, and it is the reason the paper's Problem 5.2 — does
--   $P = NP$ over $\mathbb{R}$? — is equivalent to the complexity of real feasibility.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §6, p. 27, Corollary

import Definitions.Def_BSSFeasibility

namespace BSS

theorem p_eq_np_of_feas4_inP (hF : DecisionInP Feas4 Feas4Yes) :
    ∀ Z Zyes : Set (Rinf ℝ), Zyes ⊆ Z → DecisionInNP Z Zyes → DecisionInP Z Zyes := by sorry

end BSS
