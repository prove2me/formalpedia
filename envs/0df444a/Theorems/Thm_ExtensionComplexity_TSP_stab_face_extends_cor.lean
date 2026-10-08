-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_stab_face_extends_cor
-- name    : ExtensionComplexity.TSP.stab_face_extends_cor
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:25:47.11069+00:00
-- url     : https://prove2.me/theorems/2322867e-30fa-43fb-850c-a59f2f14adf6
-- title:
--   Lemma 8 — $\mathrm{STAB}(H_n)$, $|V(H_n)|=O(n^2)$, has a face that is an extension of $\mathrm{COR}(n)$
-- statement:
--   For a graph $G=(V,E)$ the stable set polytope $\mathrm{STAB}(G)\subseteq\mathbb R^V$ is the convex hull of the characteristic vectors of the stable sets of $G$. **Lemma 8**: for each $n$ there exists a graph $H_n$ with $O(n^2)$ vertices such that $\mathrm{STAB}(H_n)$ contains a face that is an extension of $\mathrm{COR}(n)$. Precisely, there is a constant $c$ such that for every $n$ there are $m\le c\,n^2$, a graph $H$ on $m$ vertices and a face $F$ of $\mathrm{STAB}(H)$ with a linear map $\pi$ satisfying $\pi(F)=\mathrm{COR}(n)$.
--
--   With Lemma 9 this transfers the lower bound of Theorem 7 to stable set polytopes (Theorem 10).
--
--   **Formalization Note** The stable set polytope is the published definition `ChvatalPolytopes.Shared.stablePolytope` (convex hull of incidence vectors of independent sets, in $\mathbb R^V$). $O(n^2)$ is a constant $c$ independent of $n$ with $m\le c\,n^2$. The statement is for all $n$ including $n=0$, where it holds with the empty graph.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:12, Lemma 8 (STAB(G): p. 17:12, §3.3)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Polytope
import Definitions.Def_ExtensionComplexity_TSP_CutCor
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope

namespace ExtensionComplexity.TSP

/-- **Lemma 8** (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:12): for each `n` there is a
graph `H_n` with `O(n²)` vertices such that `STAB(H_n)` contains a face that is an extension of
`COR(n)`. `O(n²)` is a constant `c` with at most `c·n²` vertices, uniform in `n`. -/
theorem stab_face_extends_cor :
    ∃ c : ℕ, ∀ n : ℕ, ∃ m : ℕ, m ≤ c * n ^ 2 ∧ ∃ H : SimpleGraph (Fin m),
      ∃ F : Set (Fin m → ℝ), IsFace (ChvatalPolytopes.Shared.stablePolytope H) F ∧
        IsExtension F (corPolytope n) := by sorry

end ExtensionComplexity.TSP
