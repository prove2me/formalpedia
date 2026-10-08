-- Prove2me | Theorems.Thm_ExtensionComplexity_TSP_cor_valid_inequality_slack
-- name    : ExtensionComplexity.TSP.cor_valid_inequality_slack
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T12:25:07.501317+00:00
-- url     : https://prove2.me/theorems/27fb8bb0-5d02-49a6-a1b6-6374dbccba9a
-- title:
--   Lemma 6 — $\langle 2\,\mathrm{diag}(a)-aa^\top,x\rangle\le 1$ is valid for $\mathrm{COR}(n)$ with slack $M_{ab}$ at $bb^\top$
-- statement:
--   For $a\in\{0,1\}^n$ consider the inequality
--
--   $$\langle 2\,\mathrm{diag}(a)-aa^\top,\ x\rangle\ \le\ 1,\tag{5}$$
--
--   where $\langle X,Y\rangle=\sum_{i,j}X_{ij}Y_{ij}$ is the Frobenius inner product and $\mathrm{diag}(a)$ the diagonal matrix with $a$ on its diagonal. **Lemma 6**: for every $a\in\{0,1\}^n$,
--
--   1. inequality (5) is valid for $\mathrm{COR}(n)$, i.e. holds for every $x\in\mathrm{COR}(n)$;
--   2. the slack of the vertex $x=bb^\top$ with respect to (5) is precisely $M_{ab}$:
--   $$1-\langle 2\,\mathrm{diag}(a)-aa^\top,\ bb^\top\rangle=(1-a^\top b)^2\quad\text{for all } b\in\{0,1\}^n.$$
--
--   Hence the $2^n\times 2^n$ submatrix of a slack matrix of $\mathrm{COR}(n)$ formed by the inequalities (5) and the vertices $bb^\top$ is exactly $M(n)$.
--
--   **Formalization Note** $x\in\mathbb R^{n\times n}$ is a vector indexed by ordered pairs $(i,j)$, and the Frobenius product is the dot product over all ordered pairs.
-- source:
--   Fiorini, Massar, Pokutta, Tiwary, de Wolf, Exponential lower bounds for polytopes in combinatorial optimization, J. ACM 62(2) (2015), Art. 17, p. 17:12, Lemma 6 and inequality (5); p. 17:8, eq. (4) and footnote 5

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_CorrelationMatrix
import Definitions.Def_ExtensionComplexity_TSP_CutCor

namespace ExtensionComplexity.TSP

/-- **Lemma 6** (Fiorini et al., J. ACM 62(2) (2015), Art. 17, p. 17:12): for all `a ∈ {0,1}^n`,
the inequality `⟨2 diag(a) − aaᵀ, x⟩ ≤ 1` (5) is valid for `COR(n)`, and the slack of the vertex
`x = bbᵀ` with respect to (5) is precisely `M_ab`. `⟨·,·⟩` is the Frobenius inner product, the
sum over ordered pairs `(i, j)`. -/
theorem cor_valid_inequality_slack {n : ℕ} (a : Fin n → Bool) :
    (∀ x ∈ corPolytope n, corIneqCoeff a ⬝ᵥ x ≤ 1) ∧
      ∀ b : Fin n → Bool, 1 - corIneqCoeff a ⬝ᵥ outerBits b = matM n a b := by sorry

end ExtensionComplexity.TSP
