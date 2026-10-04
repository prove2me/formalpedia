-- Prove2me | Theorems.Thm_DiscreteConvex_NetworkFlowsC_network_transformation_zr
-- name    : DiscreteConvex.NetworkFlowsC.network_transformation_zr
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-28T03:16:56.627857+00:00
-- url     : https://prove2.me/theorems/cba72845-5929-411a-bc35-1eacccb765ed
-- title:
--   Theorem 9.27 -- network_transformation_zr
-- statement:
--   **Theorem 9.27** (p.271). The $\mathbb Z\to\mathbb R$ analogue of Theorem 9.26: (1) M-/M$^
--   atural$-convexity of $f$ transfers to $\tilde f$; (2) L-/L$^
--   atural$-convexity of $g$ transfers to $\tilde g$. The book notes the conjugacy assertion (part (3) of Theorem 9.26) is "missing in the case of $\mathbb Z\to\mathbb R$", so no analogue of it is stated here.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, Theorem 9.27.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.271, Theorem 9.27

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MExchangeAxiom
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MNaturalConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsC_SBF
import Definitions.Def_DiscreteConvex_NetworkFlowsC_TRF
import Definitions.Def_DiscreteConvex_NetworkFlowsC_LNaturalConvex
import Definitions.Def_DiscreteConvex_NetworkFlowsC_DiscreteConvexUnivariate
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTilde
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTilde
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedFTildeOnT
import Definitions.Def_DiscreteConvex_NetworkFlowsC_InducedGTildeOnT

namespace DiscreteConvex.NetworkFlowsC

open Classical
open scoped Pointwise
variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
/-- Theorem 9.27 (p.271). The `Z→R` analogue of Theorem 9.26, without an integer-valuedness or
conjugacy assertion (the book notes the conjugacy assertion is "missing in the `Z→R` case").  The induced functions are the book's functions **on `Zᵀ`** (resp. `Rᵀ`): read on
all of `Zⱽ` they are cylinders along `V ∖ T`, and the exchange axiom then fails whenever `T ≠ V`
(with `V = {s,t}`, `S = {s}`, `T = {t}`, one arc, `fa = 0` and `f` the indicator of `0`, `f̃(y) = 0`
iff `y(t) = 0`). -/
theorem network_transformation_zr (tail head : A → V) (S T : Finset V) (fa ga : A → ℤ → WithTop ℝ)
    (f g : (V → ℤ) → WithTop ℝ) (hfa : ∀ a, DiscreteConvexUnivariate (fa a))
    (hga : ∀ a, DiscreteConvexUnivariate (ga a))
    (hfbdd : ∀ y, InducedFTilde tail head S T fa f y ≠ ⊥)
    (hfprop : ∃ y, InducedFTilde tail head S T fa f y ≠ ⊤)
    (hgbdd : ∀ q, InducedGTilde tail head S T ga g q ≠ ⊥)
    (hgprop : ∃ q, InducedGTilde tail head S T ga g q ≠ ⊤) :
    (MExchangeAxiom f → MExchangeAxiom (InducedFTildeOnT tail head S T fa f)) ∧
    (MNaturalConvex f → MNaturalConvex (InducedFTildeOnT tail head S T fa f)) ∧
    ((SBF g ∧ TRF g) →
      SBF (InducedGTildeOnT tail head S T ga g) ∧ TRF (InducedGTildeOnT tail head S T ga g)) ∧
    (LNaturalConvex g → LNaturalConvex (InducedGTildeOnT tail head S T ga g)) := by sorry

end DiscreteConvex.NetworkFlowsC
