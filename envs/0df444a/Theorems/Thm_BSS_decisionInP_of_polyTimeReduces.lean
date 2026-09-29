-- Prove2me | Theorems.Thm_BSS_decisionInP_of_polyTimeReduces
-- name    : BSS.decisionInP_of_polyTimeReduces
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-14T22:10:06.717866+00:00
-- url     : https://prove2.me/theorems/41a07a49-5391-4154-a837-b1b4403eb90c
-- title:
--   $P$ over $\mathbb{R}$ is closed under polynomial time reductions
-- statement:
--   The class $P$ over $\mathbb{R}$ is closed under polynomial time reductions.
--
--   Let $(Z, Z_{\mathrm{yes}})$ and $(Y, Y_{\mathrm{yes}})$ be decision problems over $\mathbb{R}$, and suppose that $(Z, Z_{\mathrm{yes}})$ reduces to $(Y, Y_{\mathrm{yes}})$ in polynomial time: there is a machine $M_1$ over $\mathbb{R}$, in class $P$ on $Z$, whose output map $\psi = \varphi_{M_1}$ satisfies $\psi(z) \in Y$ for all $z \in Z$ and
--
--   $$\psi(z) \in Y_{\mathrm{yes}} \iff z \in Z_{\mathrm{yes}} \qquad (z \in Z).$$
--
--   Suppose moreover that $(Y, Y_{\mathrm{yes}})$ is in $P$, i.e. some machine $M_2$ in class $P$ on $Y$ halts on every $y \in Y$ with answer $1$ or $0$, answering $1$ exactly on $Y_{\mathrm{yes}}$. Then $(Z, Z_{\mathrm{yes}})$ is in $P$.
--
--   This is the composition step used in the Corollary of §6: running $M_1$ on the instance $z$ and then $M_2$ on $\psi(z)$ decides membership in $Z_{\mathrm{yes}}$, and the total cost is polynomial in $\mathrm{size}(z)$, because $\mathrm{size}(\psi(z))$ is itself bounded by a polynomial in $\mathrm{size}(z)$ — a machine running for $T$ steps can leave nonzero entries only in coordinates whose index is bounded in terms of $T$ and the size of its input. Formally the statement asserts the existence of a single machine over $\mathbb{R}$ that solves $(Z, Z_{\mathrm{yes}})$ and is in class $P$ on $Z$; its construction is the sequential composition of $M_1$ and $M_2$, in which the output of $M_1$ is re-encoded as an input state (its length placed in coordinate $0$) before $M_2$ is entered.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, section 6, p. 26, Corollary (the composition of a polynomial time reduction with a polynomial time decision procedure used in its proof)

import Definitions.Def_BSSFeasibility

namespace BSS

theorem decisionInP_of_polyTimeReduces (Z Zyes Y Yyes : Set (Rinf ℝ))
    (hred : PolyTimeReduces Z Zyes Y Yyes) (hY : DecisionInP Y Yyes) :
    DecisionInP Z Zyes := by sorry

end BSS
