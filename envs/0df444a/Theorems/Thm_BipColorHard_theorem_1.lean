-- Prove2me | Theorems.Thm_BipColorHard_theorem_1
-- name    : BipColorHard.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:36:23.354174+00:00
-- url     : https://prove2.me/theorems/087a45df-4bd1-4b9a-9309-65f6ab1da72a
-- title:
--   Theorem 1 — approximating the $q$-coloring count within $\exp(cn)$ at maximum degree $\Delta$ is NP-hard
-- statement:
--   For every fixed odd integer $q\ge5$, there is a constant $c>0$ such that, for every integer $\Delta>q$, it is NP-hard to approximate the number of proper $q$-colorings of an $n$-vertex bipartite graph of maximum degree at most $\Delta$ within a factor $\exp(cn)$. The same conclusion holds for $q=3$ and $\Delta\ge5$.
--
--   Precisely, for every NP language $L$ there are a polynomial-time map $x\mapsto G_x$ into bipartite graphs of maximum degree at most $\Delta$ and a polynomial-time answer map such that every rational $r$ with
--   $$e^{-c|V(G_x)|}Z_q(G_x)\le r\le e^{c|V(G_x)|}Z_q(G_x)$$
--   lets the answer map decide whether $x\in L$.
--
--   A proper coloring of a bipartite graph can be found in linear time, and counting bipartite colorings approximately was known to be #BIS-hard. This theorem shows that it is NP-hard, even within an exponential factor.
--
--   Differences from the source:
--   - reading: "NP-hard to approximate" → `ExpApproxNPHard`: a polynomial-time reduction from every NP language over any finite nonempty alphabet that queries the approximation once, correct for every rational answer within the factor; reason: the proof composes one query in each of Propositions 8 and 9 from a many-one gap problem; this implies hardness under polynomial-time oracle reductions
--   - encoding: $n$-vertex bipartite graph of maximum degree at most $\Delta$ → `GraphInput` on `Fin N`, `IsBipartite`, `MaxDegLe`, encoded by `encGraph`, with $n$ the vertex count of the queried graph; reason: inputs of a machine are finite strings
-- source:
--   Galanis, Guo, He, Štefankovič, Vigoda, NP-hardness for Bipartite Colorings up to the Maximum Degree, manuscript of Nov. 3, 2026 (sha256 78a66d1f…), Theorem 1, p.2 (PDF p.4)

import Definitions.Def_BipColorHard_Hardness

set_option autoImplicit false

namespace BipColorHard

/-- **Theorem 1**, p.2 (PDF p.4), Galanis, Guo, He, Štefankovič, Vigoda, *NP-hardness for Bipartite Colorings up to the Maximum Degree*, manuscript of Nov. 3, 2026 (sha256 78a66d1f…). For every
fixed odd integer `q ≥ 5`, there is a constant `c > 0` such that, for every integer `Δ > q`, it is NP-hard to approximate the number of proper `q`-colorings of an `n`-vertex bipartite graph of
maximum degree at most `Δ` within a factor `exp(cn)`. The same conclusion holds for `q = 3` and `Δ ≥ 5` as well.

**Formalization Note.** `c` is chosen before `Δ`, as in the manuscript's statement and proof. The hardness notion is `ExpApproxNPHard`, through `ColoringApproxNPHard`. -/
theorem theorem_1 :
    (∀ q : ℕ, Odd q → 5 ≤ q → ∃ c : ℝ, 0 < c ∧ ∀ Δ : ℕ, q < Δ → ColoringApproxNPHard q Δ c) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ Δ : ℕ, 5 ≤ Δ → ColoringApproxNPHard 3 Δ c) := by sorry

end BipColorHard
