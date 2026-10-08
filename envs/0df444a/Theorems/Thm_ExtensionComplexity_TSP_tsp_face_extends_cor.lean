-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_tsp_face_extends_cor
-- name    : ExtensionComplexity.TSP.tsp_face_extends_cor
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:42:28.334532+00:00
-- url     : https://prove2.me/theorems/3c044984-6c1a-4114-875f-b011bd6c92ae
-- title:
--   Lemma 11 — $\mathrm{TSP}(q)$, $q=O(n^2)$, has a face that is an extension of $\mathrm{COR}(n)$
-- statement:
--   **Lemma 11**: for each $n$ there exists a positive integer $q=O(n^2)$ such that $\mathrm{TSP}(q)$ contains a face that is an extension of $\mathrm{COR}(n)$. Precisely, there is a constant $c$ such that for every $n\ge 1$ there are an integer $q$ with $0<q\le c\,n^2$, a face $F$ of $\mathrm{TSP}(q)$ and a linear map $\pi:\mathbb R^{E_q}\to\mathbb R^{n\times n}$ with $\pi(F)=\mathrm{COR}(n)$.
--
--   With Lemma 9 and Theorem 7 this gives $\mathrm{xc}(\mathrm{TSP}(q))\ge\mathrm{xc}(\mathrm{COR}(n))\ge 2^{Cn}$ with $q=O(n^2)$, which is the main theorem.
--
--   **Formalization Note** $O(n^2)$ is a constant $c$ independent of $n$ with $q\le c\,n^2$. The hypothesis $n\ge 1$ is added: at $n=0$ no positive $q\le c\cdot 0^2$ exists. The explicit value of $q$ in the paper's proof is not part of the statement.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:14, Lemma 11

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_CutCor
import Definitions.Def_ExtensionComplexity_TSP_TSPPolytope

namespace ExtensionComplexity.TSP

/-- **Lemma 11** (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:14): for each `n` there is a
positive integer `q = O(n²)` such that `TSP(q)` contains a face that is an extension of `COR(n)`.
`O(n²)` is a constant `c` with `q ≤ c·n²`, uniform in `n`; `n ≥ 1` is added because a positive
`q ≤ c·0²` cannot exist. -/
theorem tsp_face_extends_cor :
    ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → ∃ q : ℕ, 0 < q ∧ q ≤ c * n ^ 2 ∧
      ∃ F : Set (Edge q → ℝ), IsFace (tspPolytope q) F ∧ IsExtension F (corPolytope n) := by sorry

end ExtensionComplexity.TSP
