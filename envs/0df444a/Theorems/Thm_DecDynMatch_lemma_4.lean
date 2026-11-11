-- Prove2me | Theorems.Thm_DecDynMatch_lemma_4
-- name    : DecDynMatch.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:34.559185+00:00
-- url     : https://prove2.me/theorems/2c51c42f-5503-4146-b25b-daabdd168246
-- title:
--   Lemma 4 — deferred acceptance with delayed proposals
-- statement:
--   Let $F$ be a replay rule with (12) and let $c$ be a round. Write $P=P_c$ for the market at round $c$, label its players by BUS preference, and let $\delta_i=2(i-1)$. Suppose that
--
--   1. no population event occurs in the rounds $c\le t<c+J-1$, and
--   2. every player $i\in P$ enters Work in round $c+\delta_i$.
--
--   Then the realized matching of round $c+J-2$ is the player-optimal stable matching of the market:
--   $$
--   M_{c+J-2}=m^* .
--   $$
--   This is the correctness of decentralized deferred acceptance when players start their Work modes at staggered two-round offsets; it underlies the correctness of every mature execution.
--
--   Differences from the source:
--   - generalization: utilities μ_{i,k}, π_{k,i} ∈ [0,1] → arbitrary real utilities, injective in the second argument; reason: only the strict rankings enter the protocol and the POSM; every [0,1]-valued instance is an instance here
--   - encoding: players with entry b_i ≥ 1 and departure d_i ≤ ∞, finitely many arrivals and departures → a finite type ι of all players ever active, d_i ∈ ℕ∞ with ⊤ for ∞; reason: finiteness of ι is exactly finitely many arrivals and departures; each player enters once
--   - encoding: Algorithm 1 leaves q and blockOK uninitialized → initial values q = 0, blockOK = true; reason: both are written before they are read (q at every output, blockOK at every Sweep entry), so no execution changes
--   - generalization: nondecreasing computable F : ℕ≥1 → ℕ≥1 with F(x) ≥ H + 2x → any monotone F : ℕ → ℕ with F(x) ≥ H + 2x for x ≥ 1; reason: no argument uses computability; F(0) is never evaluated (a − ℓ ≥ 1 at every output, p.14) and every rule of (12) extends monotonically by F(0) := F(1)
--   - encoding: M_t = m*_t → IsPOSM I t (M F I t); reason: strict rankings make the POSM unique, so the two agree
--   - encoding: players labeled 1, …, n by BUS preference, δ_i = 2(i − 1) → δ_i = 2 · busRank I c i, busRank = number of active players BUS prefers to i; reason: busRank is the label minus one
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Lemma 4, p.15

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_IsPOSM
import Definitions.Def_DecDynMatch_OutputsAt
import Definitions.Def_DecDynMatch_busRank

namespace DecDynMatch

/-- **Lemma 4 (Deferred Acceptance with Delayed Proposals).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), Lemma 4, p.15: "Suppose each player i enters Work at c + δᵢ, and no population event
occurs in [c, c + J − 1). Then M_{c+J−2} = m*." Setting of App. A.1, p.14: the players are those
of the market, labeled by BUS preference, δᵢ = 2(i − 1), and m* is the market's POSM.

**Formalization Note.** The market is `P_c`; `δᵢ = 2 * busRank I c i`. "m*" is the POSM of
round `c + J − 2` (the market is unchanged on `[c, c + J − 1)`). The replay rule `F` is any rule
with (12), as fixed throughout App. A. -/
theorem lemma_4 {K : ℕ} {ι : Type*} [Fintype ι] (F : ℕ → ℕ) (hF : RuleOK K F)
    (I : Instance K ι) (c : ℕ)
    (hev : NoEventIn I c (c + J K - 1))
    (hwork : ∀ i ∈ active I c, EntersWork F I (c + 2 * busRank I c i) i) :
    IsPOSM I (c + J K - 2) (M F I (c + J K - 2)) := by sorry

end DecDynMatch
