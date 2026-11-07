-- Prove2me | Theorems.Thm_ClawFreeChoosable_theorem_1_1_claw_free_perfect_chromatic_choosable
-- name    : ClawFreeChoosable.theorem_1_1_claw_free_perfect_chromatic_choosable
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:48:28.718794+00:00
-- url     : https://prove2.me/theorems/90d8cae9-4cc3-49f5-9406-793b64984fe0
-- title:
--   Theorem 1.1 — claw-free perfect graphs are chromatic-choosable
-- statement:
--   Every finite claw-free perfect graph $G$ satisfies
--   $$\mathrm{ch}(G) = \chi(G) = \omega(G),$$
--   where $\mathrm{ch}(G)$ is the choice number (the least $k$ such that every assignment of lists of at least $k$ colours admits a proper list colouring), $\chi(G)$ the chromatic number and $\omega(G)$ the clique number. The empty graph is included, with all three parameters equal to $0$.
--
--   This proves the Gravier–Maffray conjecture (every claw-free graph is chromatic-choosable) for perfect graphs, extending the List Colouring Conjecture for perfect line graphs.
--
--   Differences from the source:
--   - encoding: ch(G), χ(G), ω(G) → OAI.LinearListHadwiger.listChromaticNumber G (ℕ, cast to ℕ∞), Mathlib's chromaticNumber G (ℕ∞) and cliqueNum G (ℕ, cast to ℕ∞); reason: Lean convention; finite graphs, same values, 0 on the empty graph as in §7.1
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Theorem 1.1, p.1 (PDF p.4)

import Mathlib
import Definitions.Def_StrongPerfectGraph_Main_IsPerfect
import Definitions.Def_ListHadwiger
import Definitions.Def_ClawFreeChoosable_IsClawFree

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Theorem 1.1** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.1): every claw-free perfect graph `G` satisfies
`ch(G) = χ(G) = ω(G)`.

**Formalization Note.** Graphs are finite (`Fintype V`), the empty graph included (§7.1: its
clique, chromatic and choice numbers are `0`). `ch(G)` is the published
`OAI.LinearListHadwiger.listChromaticNumber` (least `k` such that lists of size at least `k` over
any colour type admit a proper list colouring), `χ(G)` is Mathlib's `chromaticNumber` (in `ℕ∞`)
and `ω(G)` is Mathlib's `cliqueNum`; perfection is the published
`StrongPerfectGraph.Main.IsPerfect`. Both equalities are stated, in `ℕ∞`. -/
theorem theorem_1_1_claw_free_perfect_chromatic_choosable {V : Type} [Fintype V]
    (G : SimpleGraph V) (hclaw : IsClawFree G) (hperf : StrongPerfectGraph.Main.IsPerfect G) :
    ((OAI.LinearListHadwiger.listChromaticNumber G : ℕ) : ℕ∞) = G.chromaticNumber ∧
      G.chromaticNumber = (G.cliqueNum : ℕ∞) := by sorry

end ClawFreeChoosable
