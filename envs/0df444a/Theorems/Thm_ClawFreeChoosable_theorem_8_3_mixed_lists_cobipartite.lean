-- Prove2me | Theorems.Thm_ClawFreeChoosable_theorem_8_3_mixed_lists_cobipartite
-- name    : ClawFreeChoosable.theorem_8_3_mixed_lists_cobipartite
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:45:18.476988+00:00
-- url     : https://prove2.me/theorems/e6c41cdf-be4a-440f-8ec8-8bf21883251f
-- title:
--   Theorem 8.3 — mixed lists on cobipartite graphs
-- statement:
--   Let $H$ be a finite cobipartite graph, let $C$ be an attachable clique of $H$, and let $k \ge \omega(H)$ be an integer. Then $H$ has a proper $L$-colouring for every list assignment $L$ with
--   $$|L(c)| \ge |C| \quad (c \in C), \qquad |L(v)| \ge k \quad (v \notin C).$$
--
--   The short lists on $C$ need not be related to the other lists. This is the cobipartite terminal case of the decomposition, and with $C = \emptyset$ it shows that cobipartite graphs are $\omega$-choosable.
--
--   Differences from the source:
--   - encoding: lists of colours, colorable from L → L : V → Finset α over an arbitrary colour type α; the published ListColorable; reason: Lean convention; same instances
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Theorem 8.3, p.16 (PDF p.19)

import Mathlib
import Definitions.Def_ListHadwiger
import Definitions.Def_ClawFreeChoosable_IsAttachable
import Definitions.Def_ClawFreeChoosable_IsCobipartite

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Theorem 8.3 (Mixed lists on cobipartite graphs)** (Mishra, Narayanan N, Shankar, *Claw-free perfect graphs are chromatic-choosable*, arXiv:2611.01068v1, p.16). Let `H` be a cobipartite
graph, let `C` be an attachable clique of `H`, and let `k ≥ ω(H)` be an integer. Then `H` is
colorable from every list assignment satisfying `|L(c)| ≥ |C|` (`c ∈ C`) and `|L(v)| ≥ k`
(`v ∉ C`).

**Formalization Note.** Colours range over an arbitrary type `α`; `|C|` is `Set.ncard C`;
colorability is the published `ListColorable`. -/
theorem theorem_8_3_mixed_lists_cobipartite {V : Type} [Fintype V] (H : SimpleGraph V)
    (hH : IsCobipartite H) (C : Set V) (hC : IsAttachable H C) (k : ℕ) (hk : H.cliqueNum ≤ k)
    (α : Type) (L : V → Finset α) (hLC : ∀ c ∈ C, C.ncard ≤ (L c).card)
    (hL : ∀ v, v ∉ C → k ≤ (L v).card) :
    OAI.LinearListHadwiger.ListColorable H L := by sorry

end ClawFreeChoosable
