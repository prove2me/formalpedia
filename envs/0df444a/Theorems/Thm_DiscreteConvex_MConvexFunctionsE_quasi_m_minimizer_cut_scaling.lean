-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsE_quasi_m_minimizer_cut_scaling
-- name    : DiscreteConvex.MConvexFunctionsE.quasi_m_minimizer_cut_scaling
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T00:11:40.40665+00:00
-- url     : https://prove2.me/theorems/88cea1e6-ac5a-4626-9464-cc6fc071376b
-- title:
--   Theorem 6.79 -- quasi_m_minimizer_cut_scaling
-- statement:
--   **Theorem 6.79** (Quasi M-minimizer cut with scaling; p.175). Let $f:\mathbb Z^V\to\mathbb R\cup\{+\infty\}$ satisfy (SSQM$\ne$) with $\arg\min f\ne\emptyset$, $\alpha\in\mathbb Z_{++}$, $n=|V|$. Then the two parts of Theorem 6.39 (the M-minimizer cut with scaling, already formalized as `mconvex_minimizer_cut_scaling` in mission `23-ch06c-mconvexfunctions`) hold true under this strictly weaker hypothesis.
--
--   **Formalization Note.** Restated verbatim from mission `23-ch06c-mconvexfunctions`'s Theorem 6.39 with `MExchangeAxiom` replaced by `SSQMNe`, since this mission cannot import that draft.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.175, Theorem 6.79.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.175, Theorem 6.79

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_ArgMinOn
import Definitions.Def_DiscreteConvex_MConvexFunctionsE_SSQMNe

namespace DiscreteConvex.MConvexFunctionsE

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.79 (p.175), the quasi M-minimizer cut with scaling: Theorem 6.39's two parts hold
under the weaker (SSQM≠) hypothesis. -/
theorem quasi_m_minimizer_cut_scaling (f : (V → ℤ) → WithTop ℝ) (hf : SSQMNe f)
    (hne : (ArgMinOn f).Nonempty) (alpha : ℤ) (halpha : 0 < alpha) :
    (∀ x ∈ DomZ f, ∀ v u : V,
        (∀ s : V, f (fun w => x w + alpha * (CharVec v w - CharVec u w)) ≤
          f (fun w => x w + alpha * (CharVec v w - CharVec s w))) →
        ∃ xstar ∈ ArgMinOn f,
          xstar u ≤ x u - alpha * (1 - CharVec v u) + ((Fintype.card V : ℤ) - 1) * (alpha - 1)) ∧
    (∀ x ∈ DomZ f, ∀ u v : V,
        (∀ t : V, f (fun w => x w + alpha * (CharVec v w - CharVec u w)) ≤
          f (fun w => x w + alpha * (CharVec t w - CharVec u w))) →
        ∃ xstar ∈ ArgMinOn f,
          xstar v ≥ x v + alpha * (1 - CharVec u v) - ((Fintype.card V : ℤ) - 1) * (alpha - 1)) := by sorry

end DiscreteConvex.MConvexFunctionsE
