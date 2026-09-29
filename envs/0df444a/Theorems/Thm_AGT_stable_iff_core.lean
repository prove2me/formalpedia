-- Prove2me | Theorems.Thm_AGT_stable_iff_core
-- name    : AGT.stable_iff_core
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T03:11:15.829224+00:00
-- url     : https://prove2.me/theorems/d3457a0f-991b-457b-b4c0-ea98ba402193
-- title:
--   The core of the matching game is the set of stable matchings
-- statement:
--   A matching is stable exactly when it lies in the core of the matching game (Theorem 10.12 of *Algorithmic Game Theory*): $\mu$ admits no blocking pair if and only if no coalition can rematch within itself so that every member — the men of a nonempty set $S$ and their new partners — is strictly better off.
--
--   *A note on the rendering.* One direction embeds a blocking pair $(m, w)$ as the two-agent coalition $\{m, w\}$, rematched by composing $\mu$ with the transposition of $w$ and $\mu(m)$; the other reads off a blocking pair from any member of a defecting coalition. No finiteness is needed and none is assumed: the statement holds for arbitrary sets of men and women.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 10.4.1, Theorem 10.12, pp. 257-258

import Definitions.Def_agt_matching

namespace AGT

/-- The core of the matching game is exactly the set of stable matchings
(Theorem 10.12 of *Algorithmic Game Theory*): a matching admits no
blocking pair if and only if no coalition can rematch among itself with
every member strictly better off.  One direction embeds a blocking pair as
a two-agent coalition via a transposition; the other reads off a blocking
pair from any defecting coalition.  No finiteness is needed. -/
theorem stable_iff_core {M W : Type*} (PM : M → W → W → Prop)
    (PW : W → M → M → Prop) (hM : IsPrefProfile PM) (hW : IsPrefProfile PW)
    (μ : M ≃ W) :
    IsStableMatching PM PW μ ↔ ¬ MatchDominated PM PW μ := by
  sorry

end AGT
