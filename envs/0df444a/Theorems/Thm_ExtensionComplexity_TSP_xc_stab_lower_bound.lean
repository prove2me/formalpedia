-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_xc_stab_lower_bound
-- name    : ExtensionComplexity.TSP.xc_stab_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:08:07.187253+00:00
-- url     : https://prove2.me/theorems/b89befb3-89df-4ec4-b4ff-9134d6908913
-- title:
--   Theorem 10 — graphs $G_n$ on $n$ vertices with $\mathrm{xc}(\mathrm{STAB}(G_n))=2^{\Omega(\sqrt n)}$
-- statement:
--   **Theorem 10**: for all $n$ one can construct a graph $G_n$ with $n$ vertices such that the extension complexity of the stable set polytope $\mathrm{STAB}(G_n)$ is $2^{\Omega(\sqrt n)}$. That is, there are $C>0$ and $N$ such that for every $n\ge N$ there is a graph $G$ on $n$ vertices with
--
--   $$\mathrm{xc}(\mathrm{STAB}(G))\ \ge\ 2^{C\sqrt n}.$$
--
--   The worst-case extension complexity of stable set polytopes is therefore superpolynomial, in contrast with perfect graphs, whose stable set polytopes have compact semidefinite descriptions.
--
--   **Formalization Note** "One can construct" is stated as existence of the graph. $2^{\Omega(\sqrt n)}$ is read as $\exists C>0\,\exists N\,\forall n\ge N$, with a real power. The stable set polytope is the published definition `ChvatalPolytopes.Shared.stablePolytope`.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:14, Theorem 10

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ChvatalPolytopes_Shared_StablePolytope

namespace ExtensionComplexity.TSP

/-- **Theorem 10** (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:14): for all `n` there is a
graph `G_n` with `n` vertices whose stable set polytope has extension complexity `2^{Ω(√n)}`:
there are `C > 0` and `N` such that every `n ≥ N` admits a graph `G` on `n` vertices with
`xc(STAB(G)) ≥ 2^{C√n}`. "One can construct" is stated as existence. -/
theorem xc_stab_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∃ G : SimpleGraph (Fin n),
      (2 : ℝ) ^ (C * Real.sqrt n) ≤
        (extensionComplexity (ChvatalPolytopes.Shared.stablePolytope G) : ℝ) := by sorry

end ExtensionComplexity.TSP
