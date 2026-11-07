-- Prove2me | Theorems.Thm_DraftPoA_claim_B_3
-- name    : DraftPoA.claim_B_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:16.916201+00:00
-- url     : https://prove2.me/theorems/2556a903-8796-411f-866f-0b1e35986862
-- title:
--   Claim B.3: with $F=A$, $A$ has no profitable one-shot deviation
-- statement:
--   Let $N\ge4$, $d\ge0$, $\delta'$ admissible and $b$ a completion. At every legal node $\nu$ at which an item remains and $F=A$ (damaged or not), $A$ has no profitable one-shot deviation, and her continuation value under $b$ is
--
--   $$\sum_{j\in S}\sigma_j+(h-w)\,|R'|$$
--
--   on top of her utility at $\nu$.
--
--   Once the threat is active, matching each bid of $Q$ is profitable for $A$, so the threat is credible.
--
--   Differences from the source:
--   - generalization: the instance with m(N) = N + r items and grid δ_N → every number d of dummy items and every grid δ′ ∈ {0} ∪ {δ_N/k : k ≥ 1}; reason: App. B (From N to m) and App. E (the verification does not use the bid increment) extend the check to these; d = 0, δ′ = δ_N is the source's case
--   - reading: at any node → at every legal node at which an item remains; reason: a one-shot deviation needs a round to be played
--   - generalization: no profitable one-shot deviation → also A's continuation value Σ_{j∈S} σ_j + (h − w)|R′|; reason: the proof computes it (surplus σ_{t_min} per sink item, (h − w) per rent item); Claim B.5 uses it
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), Claim B.3, p.22 (PDF 23)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_Equilibria
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- Claim B.3 (A with F = A), App. B, p.22 (PDF 23) (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

For `N ≥ 4`, any `d`, an admissible grid `δ′`, every completion `b` and every legal node `ν` at
which an item remains and `F = A` (damaged or not): `A` has no profitable one-shot deviation at
`ν`, and her continuation value under `b` is `Σ_{j∈S} σ_j + (h − w)|R′|` on top of her utility at `ν`.

**Formalization Note.** `S` and `R′` are `sinkLeft ν` and `rentLeft ν`; sink item index `x` is
sink item `x + 1`. -/
theorem claim_B_3 (N : ℕ) (hN : 4 ≤ N) (d : ℕ) {δ' : ℝ} (hδ' : IsAdmissibleGrid N δ')
    (b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) δ' 1) (hb : IsCompletion N d b)
    (ν : Node (nBid N) (mOf N + d)) (hν : IsNode δ' 1 ν) (hrem : (remaining ν).Nonempty)
    (hF : markerA ν) :
    NoProfitableOneShot (prioBad N) (vBad N d) b (bidA N) ν ∧
    uFrom (prioBad N) (vBad N d) b ν (bidA N) =
      uAt (vBad N d (bidA N)) ν (bidA N) + ∑ x ∈ sinkLeft ν, sigma N (x.val + 1) +
        (hOf N - wOf N) * ((rentLeft ν).card : ℝ) := by sorry

end DraftPoA
