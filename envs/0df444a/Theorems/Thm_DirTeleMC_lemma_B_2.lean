-- Prove2me | Theorems.Thm_DirTeleMC_lemma_B_2
-- name    : DirTeleMC.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:33:50.785207+00:00
-- url     : https://prove2.me/theorems/4bbc13ba-3efe-4c48-b9f3-9f3e7ade5627
-- title:
--   Lemma B.2 and display (2) — SCHEDULE$(J)$ informs $Y$ within $d\log_2 k/\log_2 d + \eta\theta$ rounds
-- statement:
--   Let $\ell \ge 2$, $\eta = 2\ell - 1$, and let $J$ be a structure rooted at the root of $\mathcal U_{\eta,\theta}$ that covers every terminal of a set $Y$ with $|Y| = k$. Every schedule $S$ that SCHEDULE$(J)$ can return (keeping $Y$) is a valid schedule that informs every terminal of $Y$, and:
--
--   **Lemma B.2.** for every real $d \ge 2$ with $\Lambda(J) \le d$, the length of $S$ is at most
--   $$\frac{d \log_2 k}{\log_2 d} + \eta\theta;$$
--
--   **(2)** the length of $S$ is at most $\ell \cdot \max\{\Lambda(J), k^{1/\ell}, 2\} + \eta\theta$.
--
--   Differences from the source:
--   - encoding: SCHEDULE(J) informs Y within the bound → every run of SCHEDULE(J) keeping Y is valid, informs Y, and has at most that many rounds; reason: the page leaves the breadth-first tree and ties in the child order open; every choice is covered
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Lemma B.2 and display (2), p.26 (PDF p.27)

import Mathlib
import Definitions.Def_DirTeleMC_Schedule
import Definitions.Def_DirTeleMC_IsJumpArb
import Definitions.Def_DirTeleMC_ScheduleRun

namespace DirTeleMC

/-- **Lemma B.2 and display (2)** (the length of SCHEDULE(J)).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Lemma B.2, p.26: "Let J be as in Lemma B.1, and let d ≥ 2 with Λ(J) ≤ d. Then SCHEDULE(J) informs Y within
d log₂ k/ log₂ d + ηθ rounds." and p.26: "For d = max{Λ(J), k^{1/ℓ}, 2} we have log₂ d ≥ log₂ k/ℓ, so the
length is at most ℓ · max{Λ(J), k^{1/ℓ}, 2} + ηθ. (2)"

For `ℓ ≥ 2`, `η = 2ℓ − 1`, every structure `J` rooted at the root of `U_{η,θ}` covering `Y` with `|Y| = k`, and
every run `S` of SCHEDULE(J) keeping `Y`: `S` is a valid schedule that informs every vertex of `Y`; for every real
`d ≥ 2` with `Λ(J) ≤ d` its length is at most `d log₂ k / log₂ d + ηθ`; and its length is at most
`ℓ · max{Λ(J), k^{1/ℓ}, 2} + ηθ`.

**Formalization Note.** `k = |Y|` (p.26: "so |Y| = k"). `Real.logb 2` is `log₂`; `k^{1/ℓ}` is the real power.
The length of the schedule is its number of rounds, and every vertex of the tree is informed by then. -/
theorem lemma_B_2 (I : Inst) (θ ℓ : ℕ) (hℓ : 2 ≤ ℓ) (J : JTree I.n)
    (hJ : JTree.IsStructure I.adj θ (2 * ℓ - 1) J) (hroot : J.label = I.s) (Y : Finset (Fin I.n))
    (hY : Y ⊆ JTree.cov (2 * ℓ - 1) J) (S : Schedule I.n) (hS : ScheduleRun I.s J Y S) :
    S.Valid I ∧ Y ⊆ informedAfter I.s S S.length ∧
      (∀ d : ℝ, 2 ≤ d → (J.maxLoad : ℝ) ≤ d →
        (S.length : ℝ) ≤ d * Real.logb 2 Y.card / Real.logb 2 d + ((2 * ℓ - 1) * θ : ℕ)) ∧
      (S.length : ℝ) ≤
        ℓ * max (max (J.maxLoad : ℝ) ((Y.card : ℝ) ^ ((1 : ℝ) / ℓ))) 2 + ((2 * ℓ - 1) * θ : ℕ) := by sorry

end DirTeleMC
