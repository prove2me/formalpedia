-- Prove2me | Theorems.Thm_DotySW_Deranged_finrank_walledBrauerAlgebra
-- name    : DotySW.Deranged.finrank_walledBrauerAlgebra
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:32:47.038746+00:00
-- url     : https://prove2.me/theorems/50fb65bd-36eb-4a53-aac4-32c3e945c889
-- title:
--   §3.2 — $\dim\mathcal B^{(x)}_{r,s}=(r+s)!$
-- statement:
--   For all $r,s$ and every value $\delta\in\mathbb C$ of the parameter,
--
--   $$
--   \dim_{\mathbb C}\mathcal B^{(\delta)}_{r,s}=(r+s)!.
--   $$
--
--   This fixes the size of the algebra that the mission's dimension count starts from.
--
--   **Formalization Note** The count of $(r,s)$-diagrams, and the flip bijection behind it, is the open platform theorem `WalledBrauer.SuperSchurWeyl.equation_2_1_2_2`, a reference item of this mission, and is not posed a second time. This item adds what that theorem does not say: the published left-regular realisation of the algebra has exactly that dimension, also at $\delta=0$.
--
--   Differences from the source:
--   - generalization: $\mathcal B^{(x)}_{r,s}$ with $x$ a parameter over $R[x]$ → `WalledBrauerAlgebra ℂ r s δ` for every δ : ℂ; reason: the algebra is free on the diagrams for every value of the parameter, and x = n is the case the mission uses
--   - encoding: a commutative base ring $R$ → the field ℂ; reason: §3.4 and §4 work over ℂ and the published algebra needs a field; over any $R$ the rank of the free module on the diagrams is the number of diagrams, which is the reference item `WalledBrauer.SuperSchurWeyl.equation_2_1_2_2`
-- source:
--   Doty, New versions of Schur-Weyl duality, arXiv:0704.1877v1, §3.2, unnumbered, p. 8

import Mathlib
import Definitions.Def_WalledBrauer_Blocks_Algebra

namespace DotySW.Deranged

open WalledBrauer.Blocks

/-- **The dimension of the walled Brauer algebra is `(r + s)!`.**
Doty, *New versions of Schur-Weyl duality*, arXiv:0704.1877v1, §3.2, unnumbered, p. 8.

**Formalization Note** Stated for every value `δ` of the parameter `x`, since `B^{(x)}_{r,s}` is free
on the diagrams for every `x`. The count of diagrams itself is the open platform theorem
`WalledBrauer.SuperSchurWeyl.equation_2_1_2_2` and is not posed again here. The algebra is the
published left-regular realisation, so this statement says in particular that the realisation
keeps the diagrams linearly independent, also at `δ = 0`. -/
theorem finrank_walledBrauerAlgebra (r s : ℕ) (δ : ℂ) :
    Module.finrank ℂ (WalledBrauerAlgebra ℂ r s δ) = (r + s).factorial := by sorry

end DotySW.Deranged
