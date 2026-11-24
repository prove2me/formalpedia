-- Prove2me | Theorems.Thm_FTheoryK3Tate_residual_budget
-- name    : FTheoryK3Tate.residual_budget
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-22T09:56:34.422522+00:00
-- url     : https://prove2.me/theorems/e90dbd87-5fa8-49e8-8eb5-89671dd6f455
-- title:
--   residual_budget
-- statement:
--   Residual budget. For a characteristic-zero K3-degree model, a finite set $E$ of $E_8$ (type $\mathrm{II}^*$) points, and a finite set $S$ disjoint from $E$, $10|E| + \sum_{t \in S}\operatorname{ord}_t\Delta \le 24$. In particular two $E_8$ points leave at most $4$ for the remaining fibres. Stated additively to avoid truncated subtraction.
-- source:
--   Kodaira/Tate classification of singular fibres: J. Tate (LNM 476, 1975); M. Schuett, T. Shioda, Elliptic Surfaces, arXiv:0907.0298; F-theory dictionary: T. Weigand, TASI Lectures on F-theory, arXiv:1806.01854.

import Definitions.Def_FTheoryK3TateCore
open Polynomial

namespace FTheoryK3Tate
variable {k : Type*} [Field k] [CharZero k]
/-- Corollary (residual budget). Fix a finite set `E` of `E₈` (type II*) points and a finite set
    `S` of further base points disjoint from `E`. Each `E₈` point uses `10` of the discriminant
    budget, so
    `10 * |E| + ∑_{t ∈ S} ord_t Δ ≤ 24`.
    In particular, two `E₈` points leave at most `4` for the remaining fibres. Stated additively
    to avoid truncated natural-number subtraction. -/
theorem residual_budget (f g : k[X]) (h : IsK3Data f g)
    (E S : Finset k) (hE : ∀ t ∈ E, IsE8Point f g t) (hd : Disjoint E S) :
    10 * E.card + ∑ t ∈ S, (Δ f g).rootMultiplicity t ≤ 24 := by
  sorry
end FTheoryK3Tate
