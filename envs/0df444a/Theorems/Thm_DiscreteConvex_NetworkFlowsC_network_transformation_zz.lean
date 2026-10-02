-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsC_network_transformation_zz
-- name    : DiscreteConvex.NetworkFlowsC.network_transformation_zz
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-28T03:17:09.224723+00:00
-- url     : https://prove2.me/theorems/9e91f3ac-db11-45aa-a3a7-9c7a3633e608
-- title:
--   Theorem 9.26 -- network_transformation_zz
-- statement:
--   **Theorem 9.26** (p.269-270). GOAL. For a network $G=(V,A;S,T)$ with $f_a,g_a\in C[\mathbb Z\to\mathbb Z]$, and $f,g:\mathbb Z^S\to\mathbb Z\cup\{+\infty\}$ inducing $\tilde f,\tilde g:\mathbb Z^T\to\mathbb Z\cup\{\pm\infty\}$ (assumed proper, $>-\infty$): (1) M-(resp. M$^
--   atural$-)convexity and integer-valuedness of $f$ transfer to $\tilde f$; (2) L-(resp. L$^
--   atural$-)convexity and integer-valuedness of $g$ transfer to $\tilde g$; (3) if $f$ is M$^
--   atural$-convex, $g$ is its L$^
--   atural$-convex conjugate, and each $g_a$ is the conjugate of $f_a$, then $\tilde g$ is the conjugate of $\tilde f$.
--
--   Chosen as goal: the book calls this "the harmonious relationship between network flow and M-/L-convexity", its own proof spans roughly six pages (PDF291-296), by far the longest argument in this chunk, and it underlies both Theorems 9.27-9.28 (direct analogues for other type combinations) and Notes 9.29-9.30 (the aggregation and infimal-convolution closure properties of M-convex functions, proved here as corollaries).
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269-270, Theorem 9.26.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.269-270, Theorem 9.26

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SBF
import Definitions.Def_DiscreteConvex_NetworkFlowsC_TRF
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugate
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsIntegerValuedFn
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DiscreteConvexUnivariate
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsIntegerValuedArcZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_ConvexConjugateArcZ
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTilde
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTilde
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeOnT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeOnT

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.26 (p.269-270). GOAL. For a network `G=(V,A;S,T)` with `fa,ga ∈ C[Z→Z]`, and
`f,g:Zˢ→Z∪{+∞}` inducing `f̃,g̃:Zᵀ→Z∪{±∞}` (assumed proper, `> −∞`): (1) M-(resp. M♮-)convexity
and integer-valuedness of `f` transfer to `f̃`; (2) L-(resp. L♮-)convexity and integer-valuedness
of `g` transfer to `g̃`; (3) if `f` is M♮-convex, `g` is its L♮-convex conjugate, and each `ga` is
the conjugate of `fa`, then `g̃` is the conjugate of `f̃`.  The induced functions are the book's functions **on `Zᵀ`** (resp. `Rᵀ`): read on
all of `Zⱽ` they are cylinders along `V ∖ T`, and the exchange axiom then fails whenever `T ≠ V`
(with `V = {s,t}`, `S = {s}`, `T = {t}`, one arc, `fa = 0` and `f` the indicator of `0`, `f̃(y) = 0`
iff `y(t) = 0`). -/
theorem network_transformation_zz (tail head : A → V) (S T : Finset V) (fa ga : A → ℤ → WithTop ℝ)
    (f g : (V → ℤ) → WithTop ℝ) (hfa : ∀ a, DiscreteConvexUnivariate (fa a) ∧ IsIntegerValuedArcZ (fa a))
    (hga : ∀ a, DiscreteConvexUnivariate (ga a) ∧ IsIntegerValuedArcZ (ga a))
    (hfbdd : ∀ y, InducedFTilde tail head S T fa f y ≠ ⊥)
    (hfprop : ∃ y, InducedFTilde tail head S T fa f y ≠ ⊤)
    (hgbdd : ∀ q, InducedGTilde tail head S T ga g q ≠ ⊥)
    (hgprop : ∃ q, InducedGTilde tail head S T ga g q ≠ ⊤) :
    (MExchangeAxiom f → IsIntegerValuedFn f →
      MExchangeAxiom (InducedFTildeOnT tail head S T fa f) ∧
        IsIntegerValuedFn (InducedFTildeOnT tail head S T fa f)) ∧
    (MNaturalConvex f → IsIntegerValuedFn f →
      MNaturalConvex (InducedFTildeOnT tail head S T fa f) ∧
        IsIntegerValuedFn (InducedFTildeOnT tail head S T fa f)) ∧
    ((SBF g ∧ TRF g) → IsIntegerValuedFn g →
      (SBF (InducedGTildeOnT tail head S T ga g) ∧ TRF (InducedGTildeOnT tail head S T ga g)) ∧
        IsIntegerValuedFn (InducedGTildeOnT tail head S T ga g)) ∧
    (LNaturalConvex g → IsIntegerValuedFn g →
      LNaturalConvex (InducedGTildeOnT tail head S T ga g) ∧
        IsIntegerValuedFn (InducedGTildeOnT tail head S T ga g)) ∧
    (MNaturalConvex f → LNaturalConvex g → IsIntegerValuedFn f → IsIntegerValuedFn g →
      g = ConvexConjugate f → (∀ a, ga a = ConvexConjugateArcZ (fa a)) →
      InducedGTildeOnT tail head S T ga g = ConvexConjugate (InducedFTildeOnT tail head S T fa f)) := by sorry

end DiscreteConvex.NetworkFlowsC
