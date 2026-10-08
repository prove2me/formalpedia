-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_rectangle_cover_lower_bound
-- name    : ExtensionComplexity.TSP.rectangle_cover_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:08:26.383597+00:00
-- url     : https://prove2.me/theorems/bb24dba9-6306-459a-8eeb-15f2babfcd8e
-- title:
--   Theorem 1 — every 1-rectangle cover of $\mathrm{suppmat}(M(n))$ has size $2^{\Omega(n)}$
-- statement:
--   Let $M=M(n)$ be the $2^n\times 2^n$ matrix $M_{ab}=(1-a^\top b)^2$ indexed by $n$-bit strings, and let $\mathrm{suppmat}(M)$ be its support matrix. **Theorem 1** (de Wolf 2003): every $1$-monochromatic rectangle cover of $\mathrm{suppmat}(M)$ has size $2^{\Omega(n)}$. That is, there are $C>0$ and $N$ such that for all $n\ge N$, if $R_1,\dots,R_k$ are rectangles each containing only $1$-entries of $\mathrm{suppmat}(M(n))$ and together containing all of them, then
--
--   $$k\ \ge\ 2^{Cn}.$$
--
--   Equivalently, the function $(a,b)\mapsto[a^\top b\ne 1]$ has nondeterministic communication complexity $\Omega(n)$. Combined with Theorem 4 this gives $\mathrm{rank}_+(M(n))=2^{\Omega(n)}$, the source of all lower bounds in the mission.
--
--   **Formalization Note** $2^{\Omega(n)}$ is read as: there exist $C>0$ and $N$ with $k\ge 2^{Cn}$ (real power) for all $n\ge N$. Rectangles are arbitrary pairs of sets of bit strings and may overlap.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:8, Theorem 1

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_CorrelationMatrix
import Definitions.Def_ExtensionComplexity_TSP_SlackMatrix

namespace ExtensionComplexity.TSP

/-- **Theorem 1** [de Wolf 2003] (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:8): every
1-monochromatic rectangle cover of `suppmat(M)`, `M = M(n)`, has size `2^{Ω(n)}`: there are
`C > 0` and `N` such that for every `n ≥ N`, every cover of the 1-entries of the support of
`M(n)` by `k` 1-monochromatic rectangles has `k ≥ 2^{Cn}`. -/
theorem rectangle_cover_lower_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (k : ℕ)
      (R : Fin k → Set (Fin n → Bool) × Set (Fin n → Bool)),
      IsOneRectangleCover (suppM n) R → (2 : ℝ) ^ (C * n) ≤ k := by sorry

end ExtensionComplexity.TSP
