-- Prove2me | Theorems.Thm_DecDynMatch_lemma_8
-- name    : DecDynMatch.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:51.326443+00:00
-- url     : https://prove2.me/theorems/b47ac257-2986-448c-aae9-6e1d19fc203e
-- title:
--   Lemma 8 — bounded maintenance under a general replay rule
-- statement:
--   Let $F$ be a replay rule with (12). Suppose two mature executions, at entries $c_1<c_2$ in a fixed nonempty market $P$ with POSM $m^*$, give consecutive outputs for every player, and the population remains fixed from $c_1$ on. Let $n=|P|$ and $\delta_i$ be the BUS-rank offsets. Then there are root output rounds $o_j$, common replay lengths $L_j$, window starts $Q_j=o_j+L_j$ (the root's replay deadlines) and window ends $t_j$, with $o_0=c_2+J-1$ and $t_0=c_2+J+2(n-1)$ (all players in Replay after the second execution), such that for every $j\ge 0$:
--
--   1. $t_j<Q_j<t_{j+1}\le Q_j+U$, with $U=2K^2+14K$, and $o_j\ge 1$;
--   2. the root outputs at $o_j$ and stores replay length $L_j$;
--   3. outside the maintenance window, in every round of $[t_j,Q_j)$, the realized matching is $m^*$ and all players are in Replay with the common replay length $L_j$;
--   4. the maintenance window $[Q_j,t_{j+1})$ contains a mature execution that gives every player its next output, at $o_{j+1}+\delta_i$;
--   5. $L_0\ge H$ and $L_{j+1}\ge F(L_j)$.
--
--   Differences from the source:
--   - generalization: utilities μ_{i,k}, π_{k,i} ∈ [0,1] → arbitrary real utilities, injective in the second argument; reason: only the strict rankings enter the protocol and the POSM; every [0,1]-valued instance is an instance here
--   - encoding: players with entry b_i ≥ 1 and departure d_i ≤ ∞, finitely many arrivals and departures → a finite type ι of all players ever active, d_i ∈ ℕ∞ with ⊤ for ∞; reason: finiteness of ι is exactly finitely many arrivals and departures; each player enters once
--   - encoding: Algorithm 1 leaves q and blockOK uninitialized → initial values q = 0, blockOK = true; reason: both are written before they are read (q at every output, blockOK at every Sweep entry), so no execution changes
--   - generalization: nondecreasing computable F : ℕ≥1 → ℕ≥1 with F(x) ≥ H + 2x → any monotone F : ℕ → ℕ with F(x) ≥ H + 2x for x ≥ 1; reason: no argument uses computability; F(0) is never evaluated (a − ℓ ≥ 1 at every output, p.14) and every rule of (12) extends monotonically by F(0) := F(1)
--   - encoding: M_t = m*_t → IsPOSM I t (M F I t); reason: strict rankings make the POSM unique, so the two agree
--   - encoding: players labeled 1, …, n by BUS preference, δ_i = 2(i − 1) → δ_i = 2 · busRank I c i, busRank = number of active players BUS prefers to i; reason: busRank is the label minus one
--   - encoding: maintenance windows, the common replay lengths L_j → sequences o, L, Q, t : ℕ → ℕ with windows [Q j, t (j+1)) and Replay periods [t j, Q j); reason: the windows start at the root's deadlines and end when all players are back in Replay (p.19); t is strictly increasing, so the intervals cover every round from t 0 on
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Lemma 8, p.19; maintenance windows, p.9 and p.19

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_IsPOSM
import Definitions.Def_DecDynMatch_OutputsAt
import Definitions.Def_DecDynMatch_IsMatureEntry

namespace DecDynMatch

/-- **Lemma 8 (Bounded maintenance under a general replay rule).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), Lemma 8, p.19: "Suppose two mature executions in a fixed nonempty market with
POSM m* give consecutive actual outputs for every player, and the population remains fixed
thereafter. After all players have entered Replay following the second execution, outside
maintenance windows the realized matching equals m* and all players have the same replay length.
Each window lasts at most U = 2K² + 14K rounds and contains a mature execution giving every
player's next actual output. At the end of each window, all players are in Replay with a common
replay length. Let L₀ be the common replay length after all players have entered Replay following
the second execution, and for j ≥ 1, let Lⱼ be the common replay length between the j-th and
(j + 1)-st maintenance windows. Then L₀ ≥ H, L_{j+1} ≥ F(Lⱼ) (j ≥ 0)." Maintenance windows (p.9,
p.19): "each maintenance window starts at the root's replay deadline and ends when all players have
returned to Replay after their next Work outputs".

Hypotheses: mature entries `c₁ < c₂`, no population event from `c₁` on, consecutive outputs at
`oⱼ + δᵢ` (`oⱼ = cⱼ + J − 1`). Conclusion, with `P = P_{c₁}`, `n = |P|`, `δᵢ = 2 * busRank I c₁ i`:
there are sequences `o` (root output rounds), `L` (common replay lengths), `Q = o + L` (root
deadlines, the window starts) and `t` (window ends) with `o 0 = o₂`,
`t 0 = c₂ + J + 2(n − 1)` and, for every `j`:
1. `t j < Q j < t (j+1) ≤ Q j + U`, `Q j = o j + L j`, `1 ≤ o j`;
2. the root outputs at `o j` and stores replay length `L j`;
3. in every round of `[t j, Q j)` the realized matching is the POSM and every player is in Replay
   with replay length `L j`;
4. the window `[Q j, t (j+1))` contains a mature entry `c ≥ Q j` whose execution gives every player
   its next output at `o (j+1) + δᵢ`, with `o (j+1) = c + J − 1` and `t (j+1) = c + J + 2(n − 1)`;
5. `H ≤ L 0` and `F (L j) ≤ L (j+1)`.

**Formalization Note.** Since `t` is strictly increasing, the intervals `[t j, Q j)` and
`[Q j, t (j+1))` cover every round from `t 0` on, so "outside maintenance windows" is item 3; "at
the end of each window" is item 3 at `t (j+1)`. -/
theorem lemma_8 {K : ℕ} {ι : Type*} [Fintype ι] (F : ℕ → ℕ) (hF : RuleOK K F)
    (I : Instance K ι) (c₁ c₂ : ℕ) (h12 : c₁ < c₂)
    (h1 : IsMatureEntry F I c₁) (h2 : IsMatureEntry F I c₂)
    (hev : ∀ t, c₁ ≤ t → ¬ IsEvent I t)
    (hcons : ∀ i ∈ active I c₁, NoOutputBetween F I i
      (c₁ + J K - 1 + 2 * busRank I c₁ i) (c₂ + J K - 1 + 2 * busRank I c₁ i)) :
    ∃ o L Q t : ℕ → ℕ,
      o 0 = c₂ + J K - 1 ∧
      t 0 = c₂ + J K + 2 * ((active I c₁).card - 1) ∧
      H K ≤ L 0 ∧
      ∀ j : ℕ,
        Q j = o j + L j ∧ 1 ≤ o j ∧
        t j < Q j ∧ Q j < t (j + 1) ∧ t (j + 1) ≤ Q j + U K ∧
        F (L j) ≤ L (j + 1) ∧
        (∃ r, IsRoot I c₁ r ∧ OutputsAt F I (o j) r ∧ replayLen (post F I (o j) r) = L j) ∧
        (∀ s, t j ≤ s → s < Q j →
          IsPOSM I s (M F I s) ∧
          ∀ i ∈ active I c₁, (cur F I s i).m = .replay ∧ replayLen (cur F I s i) = L j) ∧
        (∃ c, Q j ≤ c ∧ IsMatureEntry F I c ∧
          o (j + 1) = c + J K - 1 ∧
          t (j + 1) = c + J K + 2 * ((active I c₁).card - 1) ∧
          ∀ i ∈ active I c₁,
            OutputsAt F I (o (j + 1) + 2 * busRank I c₁ i) i ∧
            NoOutputBetween F I i (o j + 2 * busRank I c₁ i) (o (j + 1) + 2 * busRank I c₁ i)) := by sorry

end DecDynMatch
