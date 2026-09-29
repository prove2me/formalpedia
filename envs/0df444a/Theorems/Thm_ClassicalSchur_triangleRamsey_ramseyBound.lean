-- Prove2me | Theorems.Thm_ClassicalSchur_triangleRamsey_ramseyBound
-- name    : ClassicalSchur.triangleRamsey_ramseyBound
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:19:18.301002+00:00
-- url     : https://prove2.me/theorems/898ab4b8-2019-4b77-b707-2cfc4d644147
-- title:
--   Pigeonhole bound for triangles: $k$ colours force a monochromatic triangle on $\rho(k)$ vertices
-- statement:
--   This is the classical pigeonhole upper bound for the multicolour Ramsey numbers of triangles, in the form used in the mission.
--
--   Let $k \in \mathbb{N}$, and let $\rho$ be given by $\rho(0) = 2$ and $\rho(k+1) = (k+1)(\rho(k) - 1) + 2$, so that $\rho(0), \rho(1), \rho(2), \rho(3), \rho(4) = 2, 3, 6, 17, 66$. Let $V \subseteq \mathbb{N}$ be a finite set with $|V| \ge \rho(k)$, let $K \subseteq \mathbb{N}$ be a set of at most $k$ colours, and let $c$ be a colouring that gives every pair $x < y$ of elements of $V$ a colour $c(x, y) \in K$. Then there are $x < y < z$ in $V$ with
--
--   $$
--   c(x, y) = c(y, z) = c(x, z).
--   $$
--
--   In the notation of the Ramsey bundle, $\mathrm{TR}(k, \rho(k))$ holds for every $k$. In particular, $R_k(3) \le \rho(k)$ for every $k \ge 1$, where $R_k(3)$ is the $k$-colour Ramsey number of triangles.
--
--   This is the only Ramsey-theoretic input of the mission. At $k = 3$ it gives $R_3(3) \le 17$, which the upper bound $L(4) \le 16$ uses. At $k = 4$ it gives $R_4(3) \le 66$, which is weaker than the known bound $R_4(3) \le 62$; this is the reason for the upper bound $65$ on $L(5)$.
--
--   **Formalization Note** Eliahou and Revuelta quote the recursive bound $R_n(3) \le n(R_{n-1}(3) - 1) + 2$ for $n \ge 2$ from Greenwood and Gleason; the Lean statement iterates it from $\rho(0) = 2$ for every $k \ge 0$. For $k = 0$ no pair can receive a colour, so the statement holds vacuously. Colours are natural numbers, the colouring is a function $c : \mathbb{N} \to \mathbb{N} \to \mathbb{N}$ constrained only on the pairs $x < y$ in $V$, and the vertex set is a finite set of natural numbers in place of the vertex set of $K_N$.
-- source:
--   S. Eliahou and M. P. Revuelta, "The Schur degree of additive sets", Discrete Math. 344(5) (2021) 112332, https://doi.org/10.1016/j.disc.2021.112332 (preprint arXiv:2006.01502), §1 and §5, inequality (10) (R_n(3) ≤ n(R_{n−1}(3) − 1) + 2 for n ≥ 2, quoted from Greenwood and Gleason 1955, reference [8], Theorem 6, p. 6). A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §7 (the pigeonhole bound ρ(k), ρ(0) = 2, ρ(k+1) = (k+1)(ρ(k) − 1) + 2, in place of R_k(3)). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Ramsey.lean#L45-L87 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurRamsey
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.triangleRamsey_ramseyBound (k : ℕ) : TriangleRamsey k (ramseyBound k) := by sorry
