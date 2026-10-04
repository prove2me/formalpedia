-- Prove2me | Theorems.Thm_DiscreteConvex_MConvexFunctionsC_gs_characterizes_mconvex
-- name    : DiscreteConvex.MConvexFunctionsC.gs_characterizes_mconvex
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:43:20.212451+00:00
-- url     : https://prove2.me/theorems/876d9683-71a7-482b-ab50-de2116c85dac
-- title:
--   Theorem 6.34 -- gs_characterizes_mconvex
-- statement:
--   **Theorem 6.34** (p.154). Let $f : \mathbb Z^V \to \mathbb R\cup\{+\infty\}$ be convex extensible with a bounded nonempty effective domain. (1) If $\operatorname{dom} f \subseteq \{x : x(V)=r\}$ for some $r$, $f$ is M-convex iff it satisfies (M-GS[Z]). (2) $f$ is M$^\natural$-convex iff it satisfies (M$^\natural$-GS[Z]).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.154, Theorem 6.34.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.154, Theorem 6.34

import Mathlib
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_ConvexExtensible
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MGS
import Definitions.Def_DiscreteConvex_MConvexFunctionsC_MNatGS

namespace DiscreteConvex.MConvexFunctionsC

open scoped Pointwise
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Theorem 6.34 (p.154). -/
theorem gs_characterizes_mconvex (f : (V → ℤ) → WithTop ℝ) (hce : ConvexExtensible f)
    (hne : (DomZ f).Nonempty) (hbdd : (DomZ f).Finite) :
    ((∃ r : ℤ, ∀ x ∈ DomZ f, ∑ v, x v = r) → (MExchangeAxiom f ↔ MGS f)) ∧
    (MNaturalConvex f ↔ MNatGS f) := by sorry

end DiscreteConvex.MConvexFunctionsC
