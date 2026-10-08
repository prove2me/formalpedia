-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_xc_cor_lower_bound
-- name    : ExtensionComplexity.TSP.xc_cor_lower_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:25:28.500931+00:00
-- url     : https://prove2.me/theorems/a271da27-7086-4e56-a428-a206c4268ce8
-- title:
--   Theorem 7 — $\mathrm{xc}(\mathrm{CUT}(n+1))=\mathrm{xc}(\mathrm{COR}(n))\ge 2^{Cn}$
-- statement:
--   **Theorem 7**: there is a constant $C>0$ such that for all $n\ge 1$,
--
--   $$\mathrm{xc}(\mathrm{CUT}(n+1))=\mathrm{xc}(\mathrm{COR}(n))\ \ge\ 2^{Cn}.$$
--
--   In particular, the extension complexity of $\mathrm{CUT}(n)$ is $2^{\Omega(n)}$: there are $C'>0$ and $N$ with $\mathrm{xc}(\mathrm{CUT}(n))\ge 2^{C'n}$ for all $n\ge N$.
--
--   This is the first exponential lower bound on the extension complexity of a polytope associated with an NP-hard problem (max-cut), and it is the base of the reductions to the stable set and TSP polytopes.
--
--   **Formalization Note** The page says "for all $n$". At $n=0$ both $\mathrm{COR}(0)$ and $\mathrm{CUT}(1)$ are single points, whose extension complexity is $0<1=2^{C\cdot 0}$, so the printed statement fails there; the hypothesis $n\ge 1$ is added. The second conjunct is the "In particular" sentence, with $2^{\Omega(n)}$ read as $\exists C'>0\,\exists N\,\forall n\ge N$.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:12, Theorem 7

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_ExtensionComplexity_TSP_CutCor

namespace ExtensionComplexity.TSP

/-- **Theorem 7** (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:12): there is a constant
`C > 0` such that for all `n ≥ 1`, `xc(CUT(n+1)) = xc(COR(n)) ≥ 2^{Cn}`. In particular the
extension complexity of `CUT(n)` is `2^{Ω(n)}`. The page says "for all n"; at `n = 0` both
polytopes are single points with `xc = 0 < 2^0`, so `n ≥ 1` is added. -/
theorem xc_cor_lower_bound :
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      extensionComplexity (cutPolytope (n + 1)) = extensionComplexity (corPolytope n) ∧
        (2 : ℝ) ^ (C * n) ≤ (extensionComplexity (corPolytope n) : ℝ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N,
      (2 : ℝ) ^ (C * n) ≤ (extensionComplexity (cutPolytope n) : ℝ)) := by sorry

end ExtensionComplexity.TSP
