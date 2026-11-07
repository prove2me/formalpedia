-- Prove2me | Theorems.Thm_DraftPoA_claim_B_5
-- name    : DraftPoA.claim_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:13.695772+00:00
-- url     : https://prove2.me/theorems/1c9b1377-6dc6-4b9b-9943-06bb50e0f549
-- title:
--   Claim B.5: with $F=\emptyset$, $S\ne\emptyset$, undamaged, $A$ stays out
-- statement:
--   Let $N\ge4$, $d\ge0$, $\delta'$ admissible and $b$ a completion. At every legal undamaged node $\nu$ with $F=\emptyset$ and $S\neq\emptyset$:
--
--   1. $A$'s continuation utility under $b$ is $hr$;
--   2. every one-shot deviation of $A$ at $\nu$ whose action wins the round yields at most $\ln K+2+\delta+hr-wr$, and every one whose action loses yields $hr$;
--   3. $A$ has no profitable one-shot deviation at $\nu$.
--
--   Here $\delta=\delta_N$. Deviating gains $A$ at most $\ln K+2+\delta$ on the sink items but costs her $wr\ge\ln K+3$ of her rent.
--
--   **Formalization Note** The bounds hold for every legal bid, on every admissible grid.
--
--   Differences from the source:
--   - generalization: the instance with m(N) = N + r items and grid δ_N → every number d of dummy items and every grid δ′ ∈ {0} ∪ {δ_N/k : k ≥ 1}; reason: App. B (From N to m) and App. E (the verification does not use the bid increment) extend the check to these; d = 0, δ′ = δ_N is the source's case
--   - generalization: no profitable one-shot deviation → also the proof's bounds: ≤ ln K + 2 + δ + hr − wr for a winning action, = hr for a losing one, continuation hr; reason: the proof states them; Remark B.7 (i) uses them for every bid
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Claim B.5, pp.22–23 (PDF 23–24)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_Equilibria
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- Claim B.5 (A with F = ∅, S ≠ ∅, undamaged state), App. B, pp.22–23 (PDF 23–24) (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

For `N ≥ 4`, any `d`, an admissible grid `δ′`, every completion `b` and every legal undamaged node
`ν` with `F = ∅` and `S ≠ ∅`: `A`'s continuation utility under `b` is `hr`; every one-shot deviation
of `A` at `ν` whose action wins the round yields at most `ln K + 2 + δ + hr − wr`, and every one
whose action loses yields `hr`; hence `A` has no profitable one-shot deviation at `ν`.

**Formalization Note.** `δ` is the value-rounding increment `δ_N`, whatever the grid `δ′`. The
bounds hold for every legal bid. -/
theorem claim_B_5 (N : ℕ) (hN : 4 ≤ N) (d : ℕ) {δ' : ℝ} (hδ' : IsAdmissibleGrid N δ')
    (b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) δ' 1) (hb : IsCompletion N d b)
    (ν : Node (nBid N) (mOf N + d)) (hν : IsNode δ' 1 ν) (hF : ¬ markerA ν)
    (hS : (sinkLeft ν).Nonempty) (hund : ¬ damaged ν) :
    uFrom (prioBad N) (vBad N d) b ν (bidA N) = hOf N * rOf N ∧
    (∀ s : Strategy (nBid N) (mOf N + d) δ' 1, (∀ ν', ν' ≠ ν → s.act ν' = (b (bidA N)).act ν') →
      (winner (prioBad N) (fun j => (Function.update b (bidA N) s j).act ν) = bidA N →
        uFrom (prioBad N) (vBad N d) (Function.update b (bidA N) s) ν (bidA N) ≤
          Real.log (Kof N) + 2 + deltaOf N + hOf N * rOf N - wOf N * rOf N) ∧
      (winner (prioBad N) (fun j => (Function.update b (bidA N) s j).act ν) ≠ bidA N →
        uFrom (prioBad N) (vBad N d) (Function.update b (bidA N) s) ν (bidA N) =
          hOf N * rOf N)) ∧
    NoProfitableOneShot (prioBad N) (vBad N d) b (bidA N) ν := by sorry

end DraftPoA
