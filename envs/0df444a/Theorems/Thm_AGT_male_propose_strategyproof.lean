-- Prove2me | Theorems.Thm_AGT_male_propose_strategyproof
-- name    : AGT.male_propose_strategyproof
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-13T03:12:45.21755+00:00
-- url     : https://prove2.me/theorems/0aabe05b-98f1-4328-97f7-b668941ed3f2
-- title:
--   The male-propose mechanism is strategy-proof for the men
-- statement:
--   No man can game the male-propose mechanism: any mechanism selecting the male-optimal stable matching is strategy-proof for the men (Theorem 10.13 of *Algorithmic Game Theory*; Dubins–Freedman, Roth) — this mission's goal. Let $F$ be any mechanism that, on every profile of strict preferences, returns a male-optimal stable matching in the man-by-man sense of Gale–Shapley — the Deferred Acceptance outcome, unique by strictness, and equivalently characterized by the book's no-Pareto-improvement form of Theorem 10.11. Then for every profile, every man $m$, and every misreported ordering of the women, the wife $F$ assigns $m$ after the misreport either equals or is truly-worse than the wife $F$ assigns him under truth.
--
--   *A note on the rendering.* Only the men are protected: the women can famously manipulate the male-propose mechanism, and nothing of the sort is claimed for them. The mechanism is pinned by its defining property rather than by algorithm internals, and it is quantified before the misreport, so the witness must serve every deviation — nothing is chosen with hindsight. The hypothesis that $F$ selects male-optimal stable matchings is satisfiable by Theorem 10.11.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 10.4.2, Theorem 10.13, pp. 258-259

import Definitions.Def_agt_matching

namespace AGT

/-- The male-propose mechanism is strategy-proof for the men (Theorem 10.13
of *Algorithmic Game Theory*; Dubins–Freedman, Roth) — the capstone of the
mission.  Formally: any mechanism selecting, on every profile of strict
preferences, the male-optimal stable matching (the male-propose Deferred
Acceptance outcome, Theorem 10.11) leaves no man able to obtain a wife he
truly prefers by misreporting his ordering.  The women, famously, can
manipulate; nothing of the sort is claimed for them. -/
theorem male_propose_strategyproof {M W : Type*} [Fintype M] [Fintype W]
    [DecidableEq M]
    (F : (M → W → W → Prop) → (W → M → M → Prop) → M ≃ W)
    (hF : ∀ PM PW, IsPrefProfile PM → IsPrefProfile PW →
      IsMaleOptimal PM PW (F PM PW)) :
    ∀ PM PW, IsPrefProfile PM → IsPrefProfile PW →
      ∀ m (r' : W → W → Prop), IsStrictTotalOrder W r' →
        F (Function.update PM m r') PW m = F PM PW m ∨
          PM m (F PM PW m) (F (Function.update PM m r') PW m) := by
  sorry

end AGT
