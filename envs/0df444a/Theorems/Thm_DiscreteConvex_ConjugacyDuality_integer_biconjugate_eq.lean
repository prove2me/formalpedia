-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDuality_integer_biconjugate_eq
-- name    : DiscreteConvex.ConjugacyDuality.integer_biconjugate_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T01:11:44.322994+00:00
-- url     : https://prove2.me/theorems/7d63d7d3-f45b-45e6-8697-b45c90b78521
-- title:
--   Proposition 8.11 -- the integer biconjugate recovers f at subdifferentiable points
-- statement:
--   **Proposition 8.11** (p.212). For an integer-valued function $f : \mathbb Z^V \to \mathbb Z \cup \{+\infty\}$ and $x \in \operatorname{dom}_{\mathbb Z} f$, the integer biconjugate $f^{\bullet\bullet}(x) = f(x)$ whenever the integer subdifferential $\partial_{\mathbb Z} f(x)$ is nonempty — the fundamental fact making biconjugation meaningful for discrete functions, and a direct building block for the discrete conjugacy theorem.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Proposition 8.11.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.212, Proposition 8.11

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDuality_ConvexConjugate
import Definitions.Def_DiscreteConvex_ConjugacyDuality_SubdifferentialZ
import Definitions.Def_DiscreteConvex_ConjugacyDuality_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDuality_IsIntegerValued

namespace DiscreteConvex.ConjugacyDuality

/-- Proposition 8.11 (Murota, *Discrete Convex Analysis*, SIAM 2003, p.212). For an
integer-valued function `f : Zⱽ → Z ∪ {+∞}` and `x ∈ dom_Z f`, the integer biconjugate
`f••(x) = f(x)` whenever the integer subdifferential `∂_Z f(x)` is nonempty. -/
theorem integer_biconjugate_eq {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V → ℤ) → WithTop ℝ) (hf : IsIntegerValued f) (x : V → ℤ) (hx : x ∈ DomZ f)
    (hne : (SubdifferentialZ f x).Nonempty) :
    ConvexConjugate (ConvexConjugate f) x = f x := by sorry

end DiscreteConvex.ConjugacyDuality
