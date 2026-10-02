-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_quasi_m_minimizer_cut
-- name    : DiscreteConvex.MConvexFunctionsE.quasi_m_minimizer_cut
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:11:19.715266+00:00
-- url     : https://prove2.me/theorems/7e1c0a62-a70b-4538-9b29-0d19c1de9ce0
-- title:
--   Theorem 6.77 -- quasi_m_minimizer_cut
-- statement:
--   **Theorem 6.77** (Quasi M-minimizer cut; p.174). Let $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ satisfy (SSQM$\ne$) with $\arg\min f\ne\emptyset$. Then the three parts of Theorem 6.28 (the M-minimizer cut, already formalized as `m_minimizer_cut` in mission `06-mconvex-functions-i`) hold true under this strictly weaker hypothesis.
--
--   **Formalization Note.** Since this mission cannot import mission `06-mconvex-functions-i`'s draft, Theorem 6.28's three-part conclusion is restated verbatim here with `MExchangeAxiom` replaced by `SSQMNe`, exactly reproducing the book's own "Theorem 6.28 holds true" statement.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.174, Theorem 6.77.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.174, Theorem 6.77

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNe

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.77 (p.174), the quasi M-minimizer cut: Theorem 6.28's three parts hold under the
weaker (SSQM≠) hypothesis. -/
theorem quasi_m_minimizer_cut (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNe f)
    (hne : (ArgMinOn f).Nonempty) :
    (∀ x ∈ DomZ f, ∀ v u : V,
        (∀ s : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec v w)) →
        ∃ xs ∈ ArgMinOn f, xs u ≤ x u - 1 + CharVec v u) ∧
    (∀ x ∈ DomZ f, ∀ u v : V,
        (∀ t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec u w + CharVec t w)) →
        ∃ xs ∈ ArgMinOn f, xs v ≥ x v - CharVec u v + 1) ∧
    (∀ x ∈ DomZ f \ ArgMinOn f, ∀ u v : V,
        (∀ s t : V, f (fun w => x w - CharVec u w + CharVec v w) ≤
          f (fun w => x w - CharVec s w + CharVec t w)) →
        ∃ xs ∈ ArgMinOn f, xs u ≤ x u - 1 ∧ xs v ≥ x v + 1) := by sorry

end DiscreteConvex.MConvexFunctionsE
