-- Prove2me | Theorems.Thm_DecDynMatch_lemma_5
-- name    : DecDynMatch.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:41.391365+00:00
-- url     : https://prove2.me/theorems/15ddce4a-cbea-4eae-96fc-2be2cf382dbf
-- title:
--   Lemma 5 — correctness and output offsets of mature executions
-- statement:
--   Let $F$ be a replay rule with (12). Let $c$ be a mature entry, let $P=P_c$ with $n=|P|$ players labeled by BUS preference, $\delta_i=2(i-1)$, $o=c+J-1$ and $t_{\mathrm{end}}=c+J+2(n-1)$. Suppose no population event occurs in the rounds $c\le t\le t_{\mathrm{end}}$. Then:
--
--   1. each player $i$ starts Work at $c+\delta_i$ and outputs at $o+\delta_i$;
--   2. the realized matching is the POSM $m^*$ of the market in every round $t$ with $c+J-2\le t\le t_{\mathrm{end}}$;
--   3. $t_{\mathrm{end}}\le c+J+2K-2$;
--   4. $o+\delta_i$ is the only round of $[c,t_{\mathrm{end}}]$ in which $i$ outputs;
--   5. the arm $i$ outputs is $m^*(i)$;
--   6. $i$ enters Replay in round $o+\delta_i+1$ with that arm saved;
--   7. in round $t_{\mathrm{end}}$ all players are in Replay.
--
--   Mature executions are thus correct, and their outputs keep the BUS-rank offsets, which is what makes calibration possible.
--
--   Differences from the source:
--   - generalization: utilities μ_{i,k}, π_{k,i} ∈ [0,1] → arbitrary real utilities, injective in the second argument; reason: only the strict rankings enter the protocol and the POSM; every [0,1]-valued instance is an instance here
--   - encoding: players with entry b_i ≥ 1 and departure d_i ≤ ∞, finitely many arrivals and departures → a finite type ι of all players ever active, d_i ∈ ℕ∞ with ⊤ for ∞; reason: finiteness of ι is exactly finitely many arrivals and departures; each player enters once
--   - encoding: Algorithm 1 leaves q and blockOK uninitialized → initial values q = 0, blockOK = true; reason: both are written before they are read (q at every output, blockOK at every Sweep entry), so no execution changes
--   - generalization: nondecreasing computable F : ℕ≥1 → ℕ≥1 with F(x) ≥ H + 2x → any monotone F : ℕ → ℕ with F(x) ≥ H + 2x for x ≥ 1; reason: no argument uses computability; F(0) is never evaluated (a − ℓ ≥ 1 at every output, p.14) and every rule of (12) extends monotonically by F(0) := F(1)
--   - encoding: M_t = m*_t → IsPOSM I t (M F I t); reason: strict rankings make the POSM unique, so the two agree
--   - encoding: players labeled 1, …, n by BUS preference, δ_i = 2(i − 1) → δ_i = 2 · busRank I c i, busRank = number of active players BUS prefers to i; reason: busRank is the label minus one
--   - encoding: each player outputs m*(i) → every POSM of P_c assigns to i the arm output by i; reason: the POSM exists and is unique
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Lemma 5, p.15

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_IsPOSM
import Definitions.Def_DecDynMatch_OutputsAt
import Definitions.Def_DecDynMatch_IsMatureEntry

namespace DecDynMatch

/-- **Lemma 5 (Correctness and Output Offsets of Mature Executions).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), Lemma 5, p.15: "Suppose c is a mature entry and no population event occurs
from c through t_end = c + J + 2(n − 1). Let o = c + J − 1 be the root's output round. Player i
starts Work at c + δᵢ and outputs at o + δᵢ. The actual matching reaches m* by c + J − 2 and
remains there through t_end = o + δₙ + 1 ≤ c + J + 2K − 2. Each player outputs m*(i) exactly once
in [c, t_end] and enters Replay with that saved arm at o + δᵢ + 1. At t_end, all players have
entered Replay after their Work outputs."

The conclusion lists, for every active player `i` at `c` (with `δᵢ = 2 * busRank I c i`,
`n = |P_c|`, `o = c + J − 1`, `t_end = c + J + 2(n − 1)`):
1. `i` starts Work at `c + δᵢ` and outputs at `o + δᵢ`;
2. `Mₜ` is the POSM for every `t` with `c + J − 2 ≤ t ≤ t_end`;
3. `t_end ≤ c + J + 2K − 2`;
4. `o + δᵢ` is `i`'s only output round in `[c, t_end]`;
5. the output arm is `m*(i)` (every POSM of the market at `c` assigns it to `i`);
6. `i` enters Replay at `o + δᵢ + 1` with that arm saved;
7. at `t_end` every player is in Replay.

**Formalization Note.** "Through t_end" is `NoEventIn I c (t_end + 1)`. Modes are round-start
modes. -/
theorem lemma_5 {K : ℕ} {ι : Type*} [Fintype ι] (F : ℕ → ℕ) (hF : RuleOK K F)
    (I : Instance K ι) (c : ℕ) (hc : IsMatureEntry F I c)
    (hev : NoEventIn I c (c + J K + 2 * ((active I c).card - 1) + 1)) :
    (∀ i ∈ active I c,
      EntersWork F I (c + 2 * busRank I c i) i ∧
      OutputsAt F I (c + J K - 1 + 2 * busRank I c i) i) ∧
    (∀ t, c + J K - 2 ≤ t → t ≤ c + J K + 2 * ((active I c).card - 1) →
      IsPOSM I t (M F I t)) ∧
    c + J K + 2 * ((active I c).card - 1) ≤ c + J K + 2 * K - 2 ∧
    (∀ i ∈ active I c, ∀ t, c ≤ t → t ≤ c + J K + 2 * ((active I c).card - 1) →
      OutputsAt F I t i → t = c + J K - 1 + 2 * busRank I c i) ∧
    (∀ i ∈ active I c, ∀ m, IsPOSM I c m →
      m i = some (prop F I (c + J K - 1 + 2 * busRank I c i) i)) ∧
    (∀ i ∈ active I c,
      (pre F I (c + J K - 1 + 2 * busRank I c i + 1) i).ν = some .replay ∧
      (cur F I (c + J K - 1 + 2 * busRank I c i + 1) i).m = .replay ∧
      (cur F I (c + J K - 1 + 2 * busRank I c i + 1) i).y =
        prop F I (c + J K - 1 + 2 * busRank I c i) i) ∧
    (∀ i ∈ active I c,
      (cur F I (c + J K + 2 * ((active I c).card - 1)) i).m = .replay) := by sorry

end DecDynMatch
