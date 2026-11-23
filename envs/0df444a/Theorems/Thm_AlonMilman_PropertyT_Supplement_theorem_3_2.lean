-- Prove2me | Theorems.Thm_AlonMilman_PropertyT_Supplement_theorem_3_2
-- name    : AlonMilman.PropertyT.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:31:34.29499+00:00
-- url     : https://prove2.me/theorems/20afc41e-7658-428a-b589-55c028e3ec38
-- title:
--   Theorem 3.2 — the Cartesian powers of a fixed connected graph form a concentrated family
-- statement:
--   Let $H$ be any fixed finite connected graph, and for $i \ge 1$ let $G_i = H^i$ be the Cartesian product of $i$ copies of $H$. Then $\{G_i\}_{i \ge 1}$ is a concentrated family of graphs: there are constants $c > 0$ and $h > 0$, depending only on $H$, such that for every $i \ge 1$ and every $\rho > 0$
--
--   $$\alpha(G_i, \rho) \le c \cdot \exp\!\Big(-\Big[\frac{h\rho}{\sqrt{\operatorname{diam} G_i}}\Big]\Big),$$
--
--   where $\alpha$ is the concentration function of Definition 1.2 and $[x]$ is the integer part.
--
--   For instance, the powers of $K_2$ are the hypercubes, so the theorem contains the concentration of the family of cubes. $H$ may be any connected graph, including the one-vertex graph, for which every $G_i$ has a single vertex.
--
--   **Formalization Note** Graphs are finite `SimpleGraph`s; the family is indexed by the positive integers `ℕ+`, and $G_i$ has vertex type `Fin i → V`.
--
--   Differences from the source:
--   - reading: there exist constants c, h (Definition 1.2) → constants c > 0, h > 0; reason: with h ≤ 0 the bound holds for every family, so positivity is the only meaningful reading; requiring c > 0 changes nothing because α ≥ 0.
--   - encoding: diameter ρᵢ, which is ∞ for a disconnected graph → Mathlib's `SimpleGraph.diam`, which is 0 for one vertex and for a disconnected graph; reason: hρ/√∞ = 0 on the page and hρ/√0 = 0 in Lean, so the bound is the same; all the graphs here are connected anyway.
-- source:
--   Alon, Milman, λ1, Isoperimetric Inequalities for Graphs, and Superconcentrators, J. Combin. Theory Ser. B 38 (1985), p. 81, Theorem 3.2

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_Supplement_concentrationFun
import Definitions.Def_AlonMilman_PropertyT_Supplement_IsConcentrated
import Definitions.Def_AlonMilman_PropertyT_Supplement_boxPi

namespace AlonMilman.PropertyT.Supplement

/-- Theorem 3.2 (Alon–Milman 1985, p. 81). Let `H` be any fixed finite connected simple graph.
For `i ≥ 1` let `G_i` be the Cartesian product of `i` copies of `H`. Then `{G_i}_{i ≥ 1}` is a
concentrated family of graphs. -/
theorem theorem_3_2 {V : Type} [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (hH : H.Connected) :
    IsConcentrated (fun i : ℕ+ => Fin (i : ℕ) → V) (fun i => cartesianPower H (i : ℕ)) := by sorry

end AlonMilman.PropertyT.Supplement
