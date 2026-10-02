-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDuality_submodular_conjugate_supermodular
-- name    : DiscreteConvex.ConjugacyDuality.submodular_conjugate_supermodular
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T01:11:03.65913+00:00
-- url     : https://prove2.me/theorems/f79ff2d2-e21d-4975-b625-c989bac41bf0
-- title:
--   Theorem 8.1 -- the conjugate of a submodular function is supermodular
-- statement:
--   **Theorem 8.1** (p.206). For a submodular function $f : \mathbb R^V \to \mathbb R \cup \{+\infty\}$, the Legendre-Fenchel transform $f^\bullet$ is supermodular. The classical warm-up case for the chapter's central theme: submodularity and supermodularity are not symmetric under conjugation (the converse — the conjugate of a supermodular function need not be submodular — fails in general, as the book's own counterexample shows).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Theorem 8.1.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.206, Theorem 8.1

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_SubmodularR
import Definitions.Def_DiscreteConvex_ConjugacyDuality_SupermodularEReal
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugateR

namespace DiscreteConvex.ConjugacyDuality

/-- Theorem 8.1 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.206). For a submodular
function `f : Rⱽ → R ∪ {+∞}`, the Legendre-Fenchel transform `f•` is supermodular. -/
theorem submodular_conjugate_supermodular {V : Type*} [Fintype V] (f : (V → ℝ) → WithTop ℝ)
    (hf : SubmodularR f) :
    SupermodularEReal (ConvexConjugateR f) := by sorry

end DiscreteConvex.ConjugacyDuality
