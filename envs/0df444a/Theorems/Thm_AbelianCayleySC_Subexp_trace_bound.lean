-- Prove2me | Theorems.Thm_AbelianCayleySC_Subexp_trace_bound
-- name    : AbelianCayleySC.Subexp.trace_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:43:01.881033+00:00
-- url     : https://prove2.me/theorems/8091a840-9095-400e-8a74-c006ee183881
-- title:
--   §5, Case 3 display (p.14) — trace method: $\mathrm{mul}_{1/2}(G)\le4n/d$
-- statement:
--   Let $G$ be an undirected $d$-regular graph on $n$ vertices ($d\ge1$, self-loops allowed), and $\mathrm{mul}_{1/2}(G)$ the number of eigenvalues of its normalized Laplacian $L(G)$ that are at most $1/2$, counted with multiplicity. Then
--
--   $$\frac{\mathrm{mul}_{1/2}(G)}4\le\sum_{i=1}^{n}(1-\lambda_i)^2=\operatorname{tr}(A^2)=\frac nd,\qquad\text{so}\qquad \mathrm{mul}_{1/2}(G)\le\frac{4n}{d}.$$
--
--   In the proof of Theorem 1.2 it shows that high threshold rank forces low degree, which is what makes recovering the group affordable.
--
--   Differences from the source:
--   - generalization: the display is derived for the abelian Cayley graph G of the proof of Theorem 1.2 → every undirected d-regular graph with loops allowed; reason: the derivation uses only regularity and symmetry; an undirected abelian Cayley graph is |S|-regular and symmetric, so the Lean statement specializes to the source's
--   - encoding: mul_{1/2}/4 ⩽ n/d → mul_{1/2}(G) ≤ 4n/d; reason: equivalent for d ≥ 1
--   - encoding: d-regular graph with A(G) = (1/d)·adjacency → hypothesis d ≥ 1; reason: excludes only the case where A(G) is undefined
-- source:
--   Jake Ruotolo, Sparsest Cut on Abelian Cayley Graphs, STOC 2027 submission #1724 (October 2026), p.14, §5 (proof of Theorem 1.2), Case 3, unnumbered display after "By the trace method"

import Mathlib
import Definitions.Def_AbelianCayleySC_Subexp_RegularGraph

open Finset

namespace AbelianCayleySC.Subexp

/-- **§5, Case 3 display on p.14** (trace method). For every undirected `d`-regular graph on
`n` vertices (loops allowed), the number of normalized-Laplacian eigenvalues at most `1/2`,
counted with multiplicity, is at most `4n/d`. -/
theorem trace_bound {V : Type} [Fintype V] [DecidableEq V]
    (adj : V → V → Prop) [DecidableRel adj] (hsymm : IsUndirected adj) (d : ℕ)
    (hd : 1 ≤ d) (hreg : IsRegular adj d) :
    (mulLap adj hsymm d (1 / 2) : ℝ) ≤ 4 * (Fintype.card V : ℝ) / (d : ℝ) := by sorry

end AbelianCayleySC.Subexp
