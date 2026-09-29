-- Prove2me | Theorems.Thm_AGT_house_core_unique
-- name    : AGT.house_core_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T03:11:28.471606+00:00
-- url     : https://prove2.me/theorems/b73b108d-d040-4ebf-b50b-da74aec365f9
-- title:
--   The core of the housing market is a single allocation (Roth-Postlewaite)
-- statement:
--   The core of the housing market consists of exactly one allocation (Theorem 10.6 of *Algorithmic Game Theory*; Roth–Postlewaite). For finitely many agents, each owning one house and holding a strict preference over all houses, exactly one permutation of the houses is blocked by no coalition — where a coalition blocks by redistributing the houses its own members hold, making all members weakly and some member strictly better off. The unique core allocation is the outcome of Gale's Top Trading Cycle algorithm, whose cycle-by-cycle argument is the book's proof.
--
--   *A note on the rendering.* Uniqueness is the full $\exists!$: existence and uniqueness together. On the empty market the empty allocation is vacuously the unique core point, so no nonemptiness hypothesis is needed.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 10.3, Theorem 10.6, pp. 254-255

import Definitions.Def_agt_matching

namespace AGT

/-- The core of the house allocation problem consists of exactly one
allocation (Theorem 10.6 of *Algorithmic Game Theory*; Roth–Postlewaite).
With strict preferences, exactly one permutation of the houses is
unblocked — the outcome of the Top Trading Cycle algorithm, whose
cycle-by-cycle argument the book gives.  On the empty market the empty
allocation is vacuously the unique core point. -/
theorem house_core_unique {N : Type*} [Fintype N] [DecidableEq N]
    (P : N → N → N → Prop) (hP : IsPrefProfile P) :
    ∃! σ : N ≃ N, ¬ HouseBlocked P σ := by
  sorry

end AGT
