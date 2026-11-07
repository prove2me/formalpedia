-- Prove2me | Theorems.Thm_DynConnWC_remark_26
-- name    : DynConnWC.remark_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:41:51.608096+00:00
-- url     : https://prove2.me/theorems/89d42430-1a88-44a2-a4a6-8ca7ae650c84
-- title:
--   Remark 26 — the dictionary version: positive answers always correct, $O(m+n\log^2n)$ words
-- statement:
--   For a setup meeting the standing assumptions, in a dictionary mode (the candidate must also be a current graph edge, with or without the fingerprint test), and every outcome of the random choices:
--
--   1. All of $F_0,\dots,F_L,F_{\mathrm{final}}$ are forests of $G_t$ at the end of every update.
--   2. Every positive answer of the algorithm is correct.
--   3. Under the budget, Theorem 23's bound holds.
--   4. On $E_1\cap E_3$ alone, $F_{\mathrm{final}}$ spans $G_t$ after every update; $E_2$ and $E_4$ are not needed.
--   5. As in Lemma 24, there is a program implementing the dictionary algorithm, with unchanged time bounds, with cells touched during initialization below $Cn\log_2^2n$ and cells touched during operation $t$ below $C(m_t+n\log_2^2n)$.
--
--   These are the claims of the remark that Theorem 1's dictionary clause rests on.
--
--   Differences from the source:
--   - encoding: "the fingerprints may be omitted" → the search mode `dictNoFp`; reason: it is the same search with that one test dropped
--   - generalization: the structure of §3 with B.2's search → any selector meeting Lemma 7's specification, in clauses 1–4; reason: the argument uses only the specification
--   - reading: $O(m+n\log^2n)$ words → every cell touched during operation $t$ is below $C(m_t+n\log_2^2n)$, with $m_t$ the edge count after operation $t$; reason: this is the stronger reading (current $m$, not peak $m$), and a deletion changes $m$ by one, absorbed in $C$
--   - reading: the balanced search tree's $O(\log n)$ costs and $O(m)$ words → included in the time and space bounds of clause 5; reason: the remark's conclusion is that they stay within those bounds
--   - generalization: words of $\Theta(\log n)$ bits → every $W\ge c_0\lceil\log_2n\rceil$; reason: a program that works for all larger $W$ specializes to the source's word size
-- source:
--   King, Liu, Nie, Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time (STOC 2027 submission, preprint, sha256 9d16c13e96cde8418fd8fd9bbadff18443fe432ac60bdd3db036eb8f02635770), Remark 26, p.25 (PDF 26)

import Mathlib
import Definitions.Def_DynConnWC_Bounds

set_option autoImplicit false

namespace DynConnWC

/-- **Remark 26 (Dictionary version).** King, Liu, Nie, *Fully Dynamic Connectivity in O(log³ n) Worst-Case Update Time* (STOC 2027 submission, sha256 9d16c13e…), p.25 (PDF 26).
"Store the current graph edges in a balanced search tree, and require every decoded candidate of every
search to be a current graph edge, in addition to the existing tests. … every returned pair is a graph
edge regardless of the random choices. … all forests, including F_final, are forests of G at the end of
every update regardless of the random choices. Thus two vertices in the same tree of F_final are
connected in G, and every positive answer is correct. … Updating the search tree on a graph update and
testing one candidate each take O(log n) time, within the update and search bounds, and the search tree
uses O(m) words. The search still returns a pair whenever some threshold selects exactly one cut edge,
and the concentration bound is unchanged, so Theorem 23 still holds; the soundness events E2 and E4 are
no longer needed, and the fingerprints may be omitted."

**Formalization Note.** Clauses, for the modes `dict` and `dictNoFp` (the fingerprints omitted):
(a) on every outcome of `R`, all forests are forests of `G_t` at the end of every update, and positive
answers are correct; (b) the probability bound of Theorem 23 holds under the budget; (c) on `E1 ∩ E3`
alone, `F_final` spans `G_t`, so `E2` and `E4` are not needed. Clause (d) is the implementation: as in
Lemma 24, a program for mode `dict` with unchanged time bounds and with space `O(m + n log² n)`. -/
theorem remark_26 (d β : ℝ) (hd : 0 < d) (hβ : 0 < β) :
    (∀ {n : ℕ}, 2 ≤ n → ∀ S : AlgSetup n, S.Wf → S.mode ≠ .plain →
      (∀ (R : RandChoices S) (σ : List (PunctSketch.Update n)), PunctSketch.IsValidStream σ →
        ∀ t, t ≤ σ.length →
          (∀ i, i ≤ Lpar n → SubG ((stateAt S R σ t).F i) (Gt σ t)) ∧
          SubG (stateAt S R σ t).Ffin (Gt σ t)) ∧
      (∀ (R : RandChoices S) (ops : List (Op n)), Valid ops →
        ∀ (t : ℕ) (ht : t < ops.length) (u v : Fin n), ops[t] = .query u v →
          SameTree (stateOps S R ops t).Ffin u v → (graphAt ops t).Reachable u v) ∧
      (Budget S (T0par n d) (deltaPar n β) →
        ∀ ops : List (Op n), Valid ops → numUpdates ops ≤ T0par n d →
          1 - deltaPar n β ≤ probR S {R | AlgAllCorrect S R ops}) ∧
      (∀ (R : RandChoices S) (σ : List (PunctSketch.Update n)), PunctSketch.IsValidStream σ →
        E1 S R σ → E3 S R σ → ∀ t, t ≤ σ.length →
          IsSpanningForestOf (stateAt S R σ t).Ffin (Gt σ t))) ∧
    ∃ (Pd : Program) (C c₀ : ℕ), ∀ n, 2 ≤ n → ∀ W, c₀ * Nat.clog 2 n ≤ W →
      ∃ (S : AlgSetup n) (ρ : (ℕ → Fin (2 ^ W)) → RandChoices S),
        S.mode = .dict ∧ S.Wf ∧ Budget S (T0par n d) (deltaPar n β) ∧ PushesToUniform W S ρ ∧
        ∀ (ω : ℕ → Fin (2 ^ W)) (σ : List (Op n)), Valid σ →
          Implements W Pd n ω σ S (ρ ω) ∧ TimeBounds C W Pd n ω σ ∧
            DictSpaceBound C W Pd n ω σ := by sorry

end DynConnWC
