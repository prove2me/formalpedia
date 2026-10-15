-- Prove2me | Theorems.Thm_FarhiQAOA_Concentration_summand_zero_of_disjoint
-- name    : FarhiQAOA.Concentration.summand_zero_of_disjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:33:07.621955+00:00
-- url     : https://prove2.me/theorems/d570d4a1-3c52-4a9e-a3f5-0242af5161be
-- title:
--   Section III, p. 7, after (28) — if g(j,k) and g(j′,k′) share no qubit, the summand of (28) is 0
-- statement:
--   Let $G$ be a graph on $n$ vertices, $p\ge 0$, $\boldsymbol\gamma,\boldsymbol\beta\in\mathbb R^p$, and let $\langle jk\rangle$ and $\langle j'k'\rangle$ be edges of $G$. Write $g(j,k)$ for the set of qubits at graph distance at most $p$ from $j$ or from $k$, and similarly $g(j',k')$. If
--   $$g(j,k)\cap g(j',k')=\emptyset,$$
--   then the corresponding summand of (28) vanishes:
--   $$\langle\boldsymbol\gamma,\boldsymbol\beta|C_{\langle jk\rangle}C_{\langle j'k'\rangle}|\boldsymbol\gamma,\boldsymbol\beta\rangle-\langle\boldsymbol\gamma,\boldsymbol\beta|C_{\langle jk\rangle}|\boldsymbol\gamma,\boldsymbol\beta\rangle\,\langle\boldsymbol\gamma,\boldsymbol\beta|C_{\langle j'k'\rangle}|\boldsymbol\gamma,\boldsymbol\beta\rangle=0 .$$
--
--   In words: clause operators whose $p$-step neighbourhoods are disjoint are uncorrelated in the QAOA state. This is the locality fact (the operator (14) only involves qubits within distance $p$ of the edge, and $|s\rangle$ is a product state (17)) in the form the concentration bound uses.
--
--   **Formalization Note** Graph distance is Mathlib's extended distance `SimpleGraph.edist`, which is $+\infty$ between different connected components; a vertex of another component is never in $g(j,k)$. Expectations are sums $\sum_z |\langle z|\boldsymbol\gamma,\boldsymbol\beta\rangle|^2(\cdot)(z)$, equal to the operator expectations since the operators are diagonal. The statement holds for every $p\ge0$ and all real angles.
-- source:
--   Farhi, Goldstone, Gutmann, A Quantum Approximate Optimization Algorithm, arXiv:1411.4028v1, p. 7, Section III, after (28); light cone pp. 4–5, Section II, after (14) and (17)

import Mathlib
import Definitions.Def_FarhiQAOA_Concentration_Setting

namespace FarhiQAOA.Concentration

theorem summand_zero_of_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : ℕ) (γ β : Fin p → ℝ) (j k j' k' : Fin n) (hjk : G.Adj j k) (hjk' : G.Adj j' k')
    (hdisj : Disjoint (lightCone G p j k) (lightCone G p j' k')) :
    edgeCov G p γ β j k j' k' = 0 := by sorry

end FarhiQAOA.Concentration
