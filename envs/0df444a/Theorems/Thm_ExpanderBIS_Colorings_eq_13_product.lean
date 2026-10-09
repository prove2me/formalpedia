-- Prove2me | Theorems.Thm_ExpanderBIS_Colorings_eq_13_product
-- name    : ExpanderBIS.Colorings.eq_13_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:59.991975+00:00
-- url     : https://prove2.me/theorems/114c3e81-797b-4ba2-8c13-5e5d63cf4110
-- title:
--   (13), p. 28 — |χ_{A,B}(S)|/(|A|^m|B|^m) is the product of w_{A,B}(γ_i) over the G³-connected components γ_i of S
-- statement:
--   Let $q \ge 3$ and let $G$ be a $\Delta$-regular bipartite graph with sides of size $m$. Let $(A,B)$ be a pattern with $A$ and $B$ nonempty, and let $S \subseteq V$ have $G^3$-connected components $\gamma_1, \dots, \gamma_k$. Then
--   $$\frac{|\chi_{A,B}(S)|}{|A|^m|B|^m} = \prod_{i \in [k]} w_{A,B}(\gamma_i), \qquad w_{A,B}(\gamma) = \frac{|\chi_{A,B}(\gamma)|}{|A|^m|B|^m}.$$
--   For $S = \emptyset$ the product is empty and both sides equal $1$.
--
--   This factorization is what turns the count of colorings that are close to the pattern $(A,B)$ into a polymer partition function: summing it over sparse $S$ gives $|A|^m|B|^m\,\Xi_{A,B}(G)$.
--
--   **Formalization Note.** $A, B \ne \emptyset$ is added because the identity divides by $|A|^m|B|^m$. The components are computed in the induced subgraph $G^3[S]$, with $G^3$ defined from the extended graph distance.
-- source:
--   Jenssen, Keevash and Perkins, Algorithms for #BIS-hard problems on expander graphs, SIAM J. Comput. 49(4) (2020), author accepted manuscript, p. 28, the display after (13)

import Mathlib
import Definitions.Def_ExpanderBIS_Colorings_Setting

open Classical Finset

namespace ExpanderBIS.Colorings

theorem eq_13_product {m Δ q : ℕ} (hq : 3 ≤ q) (G : SimpleGraph (ExpanderBIS.RandomHardCore.Vertex m))
    (hG : G ∈ ExpanderBIS.RandomHardCore.Gbip m Δ) (A : Finset (Fin q)) (hA : A.Nonempty)
    (hB : (univ \ A).Nonempty) (S : Finset (ExpanderBIS.RandomHardCore.Vertex m)) :
    ((chi G q A S).card : ℝ) / ((A.card : ℝ) ^ m * ((univ \ A).card : ℝ) ^ m) =
      ∏ γ ∈ g3Components G S, colWeight G q A γ := by sorry

end ExpanderBIS.Colorings
