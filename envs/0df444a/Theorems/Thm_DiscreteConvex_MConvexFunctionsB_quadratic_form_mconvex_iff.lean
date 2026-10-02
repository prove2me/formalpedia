-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsB_quadratic_form_mconvex_iff
-- name    : DiscreteConvex.MConvexFunctionsB.quadratic_form_mconvex_iff
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:11:21.263223+00:00
-- url     : https://prove2.me/theorems/c956555b-df64-4135-aa06-e1a95d4db8d2
-- title:
--   Proposition 6.8 -- quadratic_form_mconvex_iff
-- statement:
--   **Proposition 6.8** (p.139). Let $A=(a_{ij})$ be a symmetric matrix and $f(x)=\tfrac12 x^\top A x$. (1) On $\{x \in \mathbb Z^n : \sum_i x(i)=r\}$, $f$ is M-convex iff $\{i,j\}\cap\{k,l\}=\emptyset \implies a_{ij}+a_{kl} \ge \min(a_{ik}+a_{jl}, a_{il}+a_{jk})$ (Eq. (6.25)). (2) On all of $\mathbb Z^n$, $f$ is M$^\natural$-convex iff additionally $\{i,j\}\cap\{k\}=\emptyset \implies a_{ij}\ge\min(a_{ik},a_{jk})$ (Eq. (6.27)) and $a_{ij}\ge 0$ for every $(i,j)$ (Eq. (6.28)).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.139, Proposition 6.8, Eq. (6.25)-(6.28).)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.139, Proposition 6.8

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuadraticFormRestricted
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsB_QuadraticFormTotal

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.139, Proposition 6.8, in `DiscreteConvex.MConvexFunctionsB`.
-/

namespace DiscreteConvex.MConvexFunctionsB

/-- Proposition 6.8 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.139). See the item's
`natural_language_statement` for the full statement. -/
theorem quadratic_form_mconvex_iff (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (r : ℤ) :
    (MExchangeAxiom (QuadraticFormRestricted n A r) ↔
      ∀ i j k l : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k, l} : Finset (Fin n)) →
        A i j + A k l ≥ min (A i k + A j l) (A i l + A j k)) ∧
    (MNaturalConvex (QuadraticFormTotal n A) ↔
      (∀ i j k l : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k, l} : Finset (Fin n)) →
        A i j + A k l ≥ min (A i k + A j l) (A i l + A j k)) ∧
      (∀ i j k : Fin n, Disjoint ({i, j} : Finset (Fin n)) ({k} : Finset (Fin n)) →
        A i j ≥ min (A i k) (A j k)) ∧
      (∀ i j : Fin n, A i j ≥ 0)) := by sorry

end DiscreteConvex.MConvexFunctionsB
