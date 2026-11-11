-- Prove2me | Theorems.Thm_DecDynMatch_eq_17
-- name    : DecDynMatch.eq_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:01:16.080776+00:00
-- url     : https://prove2.me/theorems/dd625734-845f-4662-91d9-f5b6d7c4cccd
-- title:
--   Eq. (17) — calibration from consecutive outputs
-- statement:
--   Let $F$ be a replay rule with (12). Let $c_1<c_2$ be mature entries in a fixed market $P$ (no population event from $c_1$ until all players have entered Replay after the second execution), with root output rounds $o_j=c_j+J-1$, and suppose every player's outputs at $o_1+\delta_i$ and $o_2+\delta_i$ are consecutive. Then for every player $i$, with entry round $b_i$, local times $a'_i,a_i$ at the two outputs and $\ell_i$ the value of $\ell$ just before the second output,
--   $$
--   a'_i=o_1+\delta_i-b_i,\qquad a_i=o_2+\delta_i-b_i,\qquad \ell_i=a'_i,\qquad a_i-\ell_i=o_2-o_1,
--   $$
--   every player stores the same replay length $L=F(o_2-o_1)$, and its global replay deadline is
--   $$
--   Q_i=o_2+\delta_i+L=Q+\delta_i, \tag{17}
--   $$
--   where $Q=o_2+L$ is the root's deadline. Players thus calibrate their replay lengths from their own output histories, without a clock or communication.
--
--   Differences from the source:
--   - generalization: utilities μ_{i,k}, π_{k,i} ∈ [0,1] → arbitrary real utilities, injective in the second argument; reason: only the strict rankings enter the protocol and the POSM; every [0,1]-valued instance is an instance here
--   - encoding: players with entry b_i ≥ 1 and departure d_i ≤ ∞, finitely many arrivals and departures → a finite type ι of all players ever active, d_i ∈ ℕ∞ with ⊤ for ∞; reason: finiteness of ι is exactly finitely many arrivals and departures; each player enters once
--   - encoding: Algorithm 1 leaves q and blockOK uninitialized → initial values q = 0, blockOK = true; reason: both are written before they are read (q at every output, blockOK at every Sweep entry), so no execution changes
--   - generalization: nondecreasing computable F : ℕ≥1 → ℕ≥1 with F(x) ≥ H + 2x → any monotone F : ℕ → ℕ with F(x) ≥ H + 2x for x ≥ 1; reason: no argument uses computability; F(0) is never evaluated (a − ℓ ≥ 1 at every output, p.14) and every rule of (12) extends monotonically by F(0) := F(1)
--   - encoding: players labeled 1, …, n by BUS preference, δ_i = 2(i − 1) → δ_i = 2 · busRank I c i, busRank = number of active players BUS prefers to i; reason: busRank is the label minus one
--   - encoding: local times, ℓ and global deadlines → fields a, l of the round-start states of the output rounds, q of the state after the second output, deadline b_i + q; reason: the local clock in round t is t − b_i and replay expires when a ≥ q
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. A.1, eq. (17), p.16

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_OutputsAt
import Definitions.Def_DecDynMatch_IsMatureEntry

namespace DecDynMatch

/-- **Calibration from consecutive outputs, eq. (17).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), App. A.1, p.16: "Consider any two mature executions in this fixed market that give
consecutive actual outputs for every player. Let o₁ < o₂ be the root's output rounds in these
executions, and let bᵢ be player i's arrival round. By Lemma 5, its local times a′ᵢ and aᵢ at the
first and second outputs satisfy a′ᵢ = o₁ + δᵢ − bᵢ, aᵢ = o₂ + δᵢ − bᵢ. Let ℓᵢ denote the value
of ℓ held by player i immediately before its second output. Consecutive actual outputs give
ℓᵢ = a′ᵢ, so each player sets the same replay length L, with aᵢ − ℓᵢ = o₂ − o₁, L = F(o₂ − o₁).
Let Q = o₂ + L be the root's global replay deadline and Qᵢ player i's global replay deadline after
its second output. These deadlines retain the output offsets: Qᵢ = o₂ + δᵢ + L = Q + δᵢ. (17)"

Hypotheses: mature entries `c₁ < c₂` (root output rounds `oⱼ = cⱼ + J − 1`), no population event
from `c₁` through the end `c₂ + J + 2(n − 1)` of the second execution, and no output of any player
strictly between its outputs at `o₁ + δᵢ` and `o₂ + δᵢ`. Conclusion for every player: the local
times at the two outputs, `ℓᵢ = a′ᵢ`, `aᵢ − ℓᵢ = o₂ − o₁`, the replay length `F(o₂ − o₁)` stored
after the second output, and the global deadline `bᵢ + q = o₂ + δᵢ + F(o₂ − o₁)`.

**Formalization Note.** `δᵢ = 2 * busRank I c₁ i`, `n = |P_{c₁}|`. Local times are read from the
round-start states of the output rounds; the replay length and deadline from the state after the
second output round (`replayLen = q − ℓ`; the global deadline is `bᵢ + q`). -/
theorem eq_17 {K : ℕ} {ι : Type*} [Fintype ι] (F : ℕ → ℕ) (hF : RuleOK K F)
    (I : Instance K ι) (c₁ c₂ : ℕ) (h12 : c₁ < c₂)
    (h1 : IsMatureEntry F I c₁) (h2 : IsMatureEntry F I c₂)
    (hev : NoEventIn I c₁ (c₂ + J K + 2 * ((active I c₁).card - 1) + 1))
    (hcons : ∀ i ∈ active I c₁, NoOutputBetween F I i
      (c₁ + J K - 1 + 2 * busRank I c₁ i) (c₂ + J K - 1 + 2 * busRank I c₁ i)) :
    ∀ i ∈ active I c₁,
      (cur F I (c₁ + J K - 1 + 2 * busRank I c₁ i) i).a =
        c₁ + J K - 1 + 2 * busRank I c₁ i - I.b i ∧
      (cur F I (c₂ + J K - 1 + 2 * busRank I c₁ i) i).a =
        c₂ + J K - 1 + 2 * busRank I c₁ i - I.b i ∧
      (cur F I (c₂ + J K - 1 + 2 * busRank I c₁ i) i).l =
        (cur F I (c₁ + J K - 1 + 2 * busRank I c₁ i) i).a ∧
      (cur F I (c₂ + J K - 1 + 2 * busRank I c₁ i) i).a -
        (cur F I (c₂ + J K - 1 + 2 * busRank I c₁ i) i).l = (c₂ + J K - 1) - (c₁ + J K - 1) ∧
      replayLen (post F I (c₂ + J K - 1 + 2 * busRank I c₁ i) i) =
        F ((c₂ + J K - 1) - (c₁ + J K - 1)) ∧
      I.b i + (post F I (c₂ + J K - 1 + 2 * busRank I c₁ i) i).q =
        (c₂ + J K - 1) + 2 * busRank I c₁ i + F ((c₂ + J K - 1) - (c₁ + J K - 1)) := by sorry

end DecDynMatch
