-- Prove2me | Theorems.Thm_Apery_tau_bound
-- name    : Apery.tau_bound
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T20:22:43.498973+00:00
-- url     : https://prove2.me/theorems/272254eb-5f9a-4b5f-9035-35ec2934a81f
-- title:
--   Bound for the Bernoulli functional: $v_p^G(\tau P) \ge \beta - 4\log_p(d+1) - v_p(24)$
-- statement:
--   **The Bernoulli-functional bound.** If $P \in \mathbb{Q}[X]$ has degree $\le d$ and its values at $0, \dots, d$ have Gauss valuation at least $\beta$, then $\tau(P) = L(P^{(3)})/24$ has Gauss valuation at least $\beta - 4\log_p(d+1) - v_p(24)$. This is `tau_bound` of `Apery/Arith/TauBound.lean`; it bounds the Bernoulli functional in terms of the integrality of the values of $P$, and is the input `tauX_direct`/`VG_polyPart_eval` use in the direct-bound chain (`Apery/Arith/DirectPoly.lean`) toward `Apery.inner_bound_cap`. **Formalization Note** `tau` is the platform definition of `Zeta5_SourcePoleFun`; `VG` of `Zeta5_SourceValToolkit`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/TauBound.lean#L119-L200 (+ BinomBasis.lean)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

namespace Apery

theorem tau_bound {P : ℚ[X]} {d : ℕ} (hd : P.natDegree ≤ d) {β : ℚ}
    (hv : ∀ m ≤ d, VG p (P.eval (m : ℚ)) β) :
    VG p (tau P) (β - 4 * Nat.log p (d + 1) - padicValNat p 24) := by
  sorry

end Apery
