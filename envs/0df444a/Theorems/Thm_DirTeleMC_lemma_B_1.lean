-- Prove2me | Theorems.Thm_DirTeleMC_lemma_B_1
-- name    : DirTeleMC.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T11:34:07.76314+00:00
-- url     : https://prove2.me/theorems/362430a0-c77b-4526-8d9c-588d87b84f7b
-- title:
--   Lemma B.1 — the arborescence built by SCHEDULE
-- statement:
--   **Lemma B.1.** Let $J$ be a structure rooted at the root of $\mathcal U_{\eta,\theta}$ (root labelled $s$) that covers every terminal of $Y$, and let $F$ be the set of arcs of its jumps. Every breadth-first out-arborescence of $(V, F)$ from $s$ pruned to $Y$ is an out-arborescence of $G$ that contains $Y$, has height at most $\eta\theta$, out-degree at most $\Lambda(J)$ at every vertex, and at most $|Y|$ leaves. Such an arborescence exists when $Y$ is nonempty.
--
--   This lemma and Lemma 3.2 bound the length of SCHEDULE$(J)$ (Lemma B.2).
--
--   Differences from the source:
--   - generalization: η = 2ℓ − 1 → any natural number η; reason: the proof does not use the value of η
--   - encoding: the out-arborescence that SCHEDULE(J) builds → every breadth-first out-arborescence of (V, F) from s pruned to Y, and existence of one for nonempty Y; reason: the page leaves the breadth-first tree open; every choice is covered
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Lemma B.1, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_DirTeleMC_IsJumpArb
import Definitions.Def_DirTeleMC_ScheduleRun

namespace DirTeleMC

/-- **Lemma B.1** (the arborescence built by SCHEDULE).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Lemma B.1, p.26: "Let J be a structure rooted at the root of U_{η,θ} that covers every terminal of Y. The
out-arborescence that SCHEDULE(J) builds contains Y, has height at most ηθ and out-degree at most Λ(J), and
has at most |Y| leaves."

For every structure `J` rooted at the root of `U_{η,θ}` (root label `s`, height `η`) that covers every vertex of
`Y`: every breadth-first out-arborescence of `(V, F)` from `s` pruned to `Y` (`F` the arcs of the jumps of `J`)
is an out-arborescence of `G` that contains `Y`, has height at most `ηθ`, out-degree at most `Λ(J)` and at most
`|Y|` leaves; and such an arborescence exists when `Y` is nonempty.

**Formalization Note.** `η` is any depth (the paper's `η = 2ℓ − 1`). -/
theorem lemma_B_1 {n : ℕ} (adj : Fin n → Fin n → Bool) (θ η : ℕ) (s : Fin n) (J : JTree n)
    (hJ : JTree.IsStructure adj θ η J) (hroot : J.label = s) (Y : Finset (Fin n))
    (hY : Y ⊆ JTree.cov η J) :
    (Y.Nonempty → ∃ A : Arb n, IsPrunedSPT J.arcAdj s Y A) ∧
    ∀ A : Arb n, IsPrunedSPT J.arcAdj s Y A →
      A.IsIn adj ∧ Y ⊆ A.verts ∧ A.height ≤ η * θ ∧ A.OutDegLE J.maxLoad ∧
        A.leaves.card ≤ Y.card := by sorry

end DirTeleMC
