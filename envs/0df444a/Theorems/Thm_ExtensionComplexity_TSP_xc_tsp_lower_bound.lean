-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_xc_tsp_lower_bound
-- name    : ExtensionComplexity.TSP.xc_tsp_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:42:46.225178+00:00
-- url     : https://prove2.me/theorems/9d04b0c6-5f7a-4f58-a2d3-ddc1006d82bc
-- title:
--   Theorem 12 — the extension complexity of the TSP polytope $\mathrm{TSP}(n)$ is $2^{\Omega(\sqrt n)}$
-- statement:
--   Let $\mathrm{TSP}(n)\subseteq\mathbb R^{E_n}$ be the convex hull of the characteristic vectors of the tours (Hamiltonian cycles) of the complete graph $K_n$, and $\mathrm{xc}$ the extension complexity, the minimum number of inequalities in a linear system $E^{=}x+F^{=}y=g^{=}$, $E^{\le}x+F^{\le}y\le g^{\le}$ whose projection onto the $x$-variables is the polytope. **Theorem 12**: the extension complexity of $\mathrm{TSP}(n)$ is $2^{\Omega(\sqrt n)}$; that is, there are $C>0$ and $N$ such that
--
--   $$\mathrm{xc}(\mathrm{TSP}(n))\ \ge\ 2^{C\sqrt n}\qquad\text{for all } n\ge N.$$
--
--   This answers Yannakakis's question of 1988/1991: no linear program of subexponential size, symmetric or not, projects onto the TSP polytope.
--
--   **Formalization Note** $2^{\Omega(\sqrt n)}$ is read as $\exists C>0\,\exists N\,\forall n\ge N$, with $2^{C\sqrt n}$ a real power. The extension complexity is a natural number (the least size of an EF), so the bound cannot hold vacuously through an infinite value.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:16, Theorem 12

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_TSPPolytope

namespace ExtensionComplexity.TSP

/-- **Theorem 12** (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:16): the extension complexity
of the TSP polytope `TSP(n)` is `2^{Ω(√n)}`: there are `C > 0` and `N` with
`xc(TSP(n)) ≥ 2^{C√n}` for every `n ≥ N`. -/
theorem xc_tsp_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      (2 : ℝ) ^ (C * Real.sqrt n) ≤ (extensionComplexity (tspPolytope n) : ℝ) := by sorry

end ExtensionComplexity.TSP
