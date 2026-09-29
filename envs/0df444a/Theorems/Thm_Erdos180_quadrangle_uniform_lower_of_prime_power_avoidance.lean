-- Prove2me | Theorems.Thm_Erdos180_quadrangle_uniform_lower_of_prime_power_avoidance
-- name    : Erdos180.quadrangle_uniform_lower_of_prime_power_avoidance
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:09:42.310719+00:00
-- url     : https://prove2.me/theorems/951ac643-2f19-4bcc-b56d-0ea6b0ff83a7
-- title:
--   Quantitative lower bound from a quadrangle witness
-- statement:
--   Let $F$ be a graph without isolated vertices, let $t \in \{2,3\}$ be a prime with
--   $t^3 \le 27$, and suppose $F$ does not embed into the incidence graph of $W(t^j)$ for any
--   $j \ge 1$. Then for every $n$ at least the vertex count of the quadrangle,
--
--   $$2^{-4/3} \cdot 27^{-4/3} \cdot n^{4/3} \;\le\; \mathrm{ex}(n, F).$$
--
--   This is the quantitative core of Proposition 4.3 of the source. One chooses the largest
--   admissible $q = t^{j}$ with $n_q \le n$; since $n_{tq} \le t^3 n_q$, this loses only the factor
--   $t^3 \le 27$, so $n_q \gg n$, and equation (8) gives $e_q \ge 2^{-4/3} n_q^{4/3}$ edges. Padding
--   with isolated vertices extends the construction from $n_q$ to $n$. $W(q)$ denotes the symplectic generalized quadrangle over $\mathbb{F}_q$, whose points are the $1$-dimensional and whose lines are the totally isotropic $2$-dimensional subspaces of $\mathbb{F}_q^4$, and $I_q$ its bipartite point-line incidence graph. $I_q$ has girth eight, $n_q = 2(q+1)(q^2+1)$ vertices and $e_q = (q+1)^2(q^2+1) \ge 2^{-4/3} n_q^{4/3}$ edges (§4 of the source).
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2945-L2981

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.FieldTheory.Finite.GaloisField

open Erdos180
open SimpleGraph

theorem Erdos180.quadrangle_uniform_lower_of_prime_power_avoidance
    {U : Type*} (forbidden : SimpleGraph U)
    (hneighbors : ∀ u : U, ∃ v : U, forbidden.Adj u v)
    (t : ℕ) [Fact t.Prime]
    (ht : 2 ≤ t) (htgap : t ^ 3 ≤ 27)
    (hfree : ∀ j : ℕ, 0 < j →
      forbidden.Free (symplecticQuadrangle (GaloisField t j)))
    {n : ℕ} (hn : quadrangleVertexCount t ≤ n) :
    ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (27 : ℝ) ^ (-((4 : ℝ) / 3))) *
      (n : ℝ) ^ ((4 : ℝ) / 3) ≤
        (SimpleGraph.extremalNumber n forbidden : ℝ) := by sorry
