-- Prove2me | Theorems.Thm_DLSConsensus_BasicRound_lemma_3_2
-- name    : DLSConsensus.BasicRound.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:43:38.574669+00:00
-- url     : https://prove2.me/theorems/5aa5ff92-2c22-4555-b05c-989e0b23b7f3
-- title:
--   Lemma 3.2 — after the first decision, at least t + 1 processors keep a lock on the decided value
-- statement:
--   Consider any run of Algorithm 1 in the basic round model with $t\le N$, arbitrary initial values and delivery pattern, and an admissible choice function. Suppose some processor $p$ (correct or faulty) decides $v$ at phase $k$, and no processor decides any value at a phase $k'<k$. Then:
--
--   1. at least $t+1$ processors lock $v$ at phase $k$, that is,
--   $$\bigl|\{\,q : q \text{ receives } (\mathrm{lock}\ v,k) \text{ in round } 4k-2\,\}\bigr| \ \ge\ t+1;$$
--   2. each processor $q$ that locks $v$ at phase $k$ has, after every round $r\ge 4k-2$, a lock on $v$ whose associated phase number $h$ satisfies $h\ge k$.
--
--   This lemma is the core of the consistency argument for Algorithm 1: the $t+1$ persistent locks on $v$ prevent any other value from being found acceptable by $N-t$ processors at a later phase.
--
--   **Formalization Note** "From that time onward" is read as: after the computation subround of round $4k-2$ and of every later round. The lemma is about the decisions of all processors, not only correct ones, since omission-faulty processors also run the algorithm. The hypothesis $t\le N$ makes the threshold $N-t$ meaningful (natural-number subtraction).
-- source:
--   Dwork, Lynch, Stockmeyer, Consensus in the presence of partial synchrony, J. ACM 35 (1988), p. 297, Lemma 3.2

import Mathlib
import Definitions.Def_DLSConsensus_BasicRound_Model

namespace DLSConsensus.BasicRound

/-- Lemma 3.2 (p. 297): if some processor (correct or not) decides `v` at phase `k`, and no
processor decides anything at a phase `< k`, then at least `t + 1` processors lock `v` at
phase `k`, and each processor that locks `v` at phase `k` has, after every round
`r ≥ 4k - 2`, a lock on `v` with associated phase at least `k`. -/
theorem lemma_3_2 {N : ℕ} {V : Type*} (t : ℕ) (ht : t ≤ N) (pick : ℕ → Set V → V)
    (hpick : PickAdmissible pick) (init : Fin N → V) (deliv : ℕ → Fin N → Fin N → Prop)
    (p : Fin N) (k : ℕ) (v : V) (hdec : DecidesAt t pick init deliv p k v)
    (hmin : ∀ k' < k, ∀ (q : Fin N) (w : V), ¬ DecidesAt t pick init deliv q k' w) :
    t + 1 ≤ (Lockers t pick init deliv k v).card ∧
      ∀ q : Fin N, LocksAt t pick init deliv q k v →
        ∀ r : ℕ, 4 * k - 2 ≤ r →
          ∃ h : ℕ, k ≤ h ∧ (exec t pick init deliv r q).lock v = some h := by sorry

end DLSConsensus.BasicRound
