-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_cor_linearly_isomorphic_cut
-- name    : ExtensionComplexity.TSP.cor_linearly_isomorphic_cut
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:24:58.750607+00:00
-- url     : https://prove2.me/theorems/da4f1e11-14ac-4d14-8411-cf18e4ef2952
-- title:
--   Theorem 5 (De Simone) — $\mathrm{COR}(n)$ is linearly isomorphic to $\mathrm{CUT}(n+1)$
-- statement:
--   **Theorem 5** (De Simone 1990): for every $n$, the correlation polytope $\mathrm{COR}(n)\subseteq\mathbb R^{n\times n}$ is linearly isomorphic to the cut polytope $\mathrm{CUT}(n+1)\subseteq\mathbb R^{E_{n+1}}$. Precisely: there is an injective linear map
--
--   $$L:\mathbb R^{E_{n+1}}\to\mathbb R^{n\times n}\qquad\text{with}\qquad L(\mathrm{CUT}(n+1))=\mathrm{COR}(n).$$
--
--   Because $L$ is a linear isomorphism onto its image, EFs of either polytope transfer to the other with the same number of inequalities, so the two polytopes have the same extension complexity (the equality in Theorem 7).
--
--   **Formalization Note** The paper calls two polytopes linearly isomorphic if one is obtained from the other by an invertible linear map. Here the ambient spaces have dimensions $n(n+1)/2$ and $n^2$, so no invertible map between them exists; the statement uses an injective linear map, which is invertible onto its image. A non-injective map would not suffice and is excluded.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:12, Theorem 5 (linear isomorphism: p. 17:11)

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_CutCor

namespace ExtensionComplexity.TSP

/-- **Theorem 5** [De Simone 1990] (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:12): for all
`n`, `COR(n)` is linearly isomorphic to `CUT(n+1)`. Since `CUT(n+1) ⊆ ℝ^{E_{n+1}}` and
`COR(n) ⊆ ℝ^{n×n}` live in spaces of different dimensions, this is read as: an injective linear map
`ℝ^{E_{n+1}} → ℝ^{n×n}` (a linear isomorphism onto its image) carries `CUT(n+1)` onto `COR(n)`. -/
theorem cor_linearly_isomorphic_cut (n : ℕ) :
    ∃ L : (Edge (n + 1) → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ),
      Function.Injective L ∧ L '' cutPolytope (n + 1) = corPolytope n := by sorry

end ExtensionComplexity.TSP
