-- Prove2me | Theorems.Thm_DiscreteConvex_ConjugacyDualityD_lagrangian_kernel_formula
-- name    : DiscreteConvex.ConjugacyDualityD.lagrangian_kernel_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-28T02:02:37.583902+00:00
-- url     : https://prove2.me/theorems/4deea6d7-90a1-4145-8dc1-9399903efa21
-- title:
--   Proposition 8.56 -- lagrangian_kernel_formula
-- statement:
--   **Proposition 8.56**, part (1) (p.239). For $x\in\operatorname{dom} c$, the unregularized Lagrangian kernel has the closed form $K_0(x,y) = c(x) - \langle x,y\rangle - \delta_B^{\bullet}(-y)$, expressing it via the convex conjugate of the indicator function of $B$.
--
--   **Scope reduction.** This chunk omits part (2) of Proposition 8.56 (the closed form for the regularized kernel $K_r$ in terms of the infimal convolution $\delta_{-B}\square r[y]$), which needs infimal-convolution notation not independently required elsewhere in this chunk; see `HARD.md`.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.239, Proposition 8.56.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.239, Proposition 8.56

import Mathlib
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_DomZ
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ToEReal
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_IndicatorWT
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_ConvexConjE
import Definitions.Def_DiscreteConvex_ConjugacyDualityD_KR

namespace DiscreteConvex.ConjugacyDualityD

open Classical
open scoped Pointwise
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Proposition 8.56 (p.239), part (1). A closed form for `K0(x,y)` on `dom c`, via the conjugate
of the indicator function of `B`. -/
theorem lagrangian_kernel_formula (c : (V → ℤ) → WithTop ℝ) (B : Set (V → ℤ)) (x y : V → ℤ)
    (hx : x ∈ DomZ c) :
    KR c (fun _ => (0 : WithTop ℝ)) B x y =
      ToEReal (c x) - ((∑ i, (x i : ℝ) * (y i : ℝ) : ℝ) : EReal) -
        ConvexConjE (fun z => ToEReal (IndicatorWT B z)) (fun v => -y v) := by sorry

end DiscreteConvex.ConjugacyDualityD
