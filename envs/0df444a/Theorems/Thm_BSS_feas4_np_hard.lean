-- Prove2me | Theorems.Thm_BSS_feas4_np_hard
-- name    : BSS.feas4_np_hard
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T15:14:09.082927+00:00
-- url     : https://prove2.me/theorems/70f41ee1-4710-40c1-b37e-e8445bb38fe5
-- title:
--   §6: every problem in $NP$ over $\mathbb{R}$ reduces to 4-Feasibility
-- statement:
--   The hardness half of the Main Theorem of §6 (p. 26). Given a decision problem
--   $(Z, Z_{\mathrm{yes}})$ in $NP$ over $\mathbb{R}$ with nondeterministic machine $M$ and bound
--   $T_0(z) = c\,\mathrm{size}(z)^q$, one writes down the time-$T_0(z)$ halting equations for $M$ on
--   $(z, z')$ together with the equations recording that the input is $(z, z')$ and that the answer is
--   yes. By the Lemma of §6 this system has a solution exactly when $z \in Z_{\mathrm{yes}}$, and by
--   the Theorem of §4 it collapses to a single polynomial of degree at most $4$, giving the map
--   $\psi$. That $\psi$ is polynomial time computable is the quantitative part: $T_0(z)$ is polynomial
--   in the size of $z$, and the length of the powerfree representation of $\psi(z)$ is polynomial in
--   $T_0(z)$ by the counting of §§3–4.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §6, p. 26, Main Theorem (hardness half), with the Lemma on p. 26

import Definitions.Def_BSSFeasibility

namespace BSS

theorem feas4_np_hard :
    ∀ Z Zyes : Set (Rinf ℝ), Zyes ⊆ Z → DecisionInNP Z Zyes →
      PolyTimeReduces Z Zyes Feas4 Feas4Yes := by sorry

end BSS
