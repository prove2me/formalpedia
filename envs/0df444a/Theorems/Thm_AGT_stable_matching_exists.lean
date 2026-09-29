-- Prove2me | Theorems.Thm_AGT_stable_matching_exists
-- name    : AGT.stable_matching_exists
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T03:10:49.730381+00:00
-- url     : https://prove2.me/theorems/1af5174c-0d52-4d3d-a5f8-7f1143262123
-- title:
--   Stable matchings exist (Gale-Shapley)
-- statement:
--   Every marriage market has a stable matching — Gale–Shapley, rendered from Theorem 10.10 of *Algorithmic Game Theory*. For finite sets of men and women with strict preferences over the opposite side and $|M| = |W|$ (the hypothesis $\mathrm{Nonempty}(M \simeq W)$, which the book arranges by dummy partners), some bijection $\mu : M \simeq W$ admits no blocking pair: no man and woman both prefer each other to their assigned partners.
--
--   *A note on the rendering.* The book's Theorem 10.10 states that the male-propose Deferred Acceptance Algorithm terminates in a stable matching; the algorithm is the book's proof device, and this milestone asserts its existence content. A solver may formalize deferred acceptance and its termination, or reach existence by any other route — the fixed-point formulation the book sketches as Theorem 10.14 (via Tarski), for instance.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 10.4, Theorem 10.10, pp. 256-257

import Definitions.Def_agt_matching

namespace AGT

/-- A stable matching always exists (Gale–Shapley; Theorem 10.10 of
*Algorithmic Game Theory* — the book obtains it as the terminal state of
the male-propose Deferred Acceptance Algorithm).  The hypothesis
`Nonempty (M ≃ W)` is the book's standing convention `|M| = |W|`, arranged
there by dummy partners; with no bijection at all there are no matchings
to speak of. -/
theorem stable_matching_exists {M W : Type*} [Fintype M] [Fintype W]
    (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (hM : IsPrefProfile PM) (hW : IsPrefProfile PW)
    (hcard : Nonempty (M ≃ W)) :
    ∃ μ : M ≃ W, IsStableMatching PM PW μ := by
  sorry

end AGT
