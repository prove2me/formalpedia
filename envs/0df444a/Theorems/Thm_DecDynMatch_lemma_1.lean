-- Prove2me | Theorems.Thm_DecDynMatch_lemma_1
-- name    : DecDynMatch.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:49.371895+00:00
-- url     : https://prove2.me/theorems/128b8b58-625d-4b21-90c1-9207bdcd7af1
-- title:
--   Lemma 1 — recovery and calibration (every replay rule with (12))
-- statement:
--   Let $F$ be a replay rule with (12) and let $I$ be an instance with nonempty final market $P=P_{t^*}$, $n=|P|$, players labeled by BUS preference. Then each player $i\in P$ finishes two consecutive Work modes initiated after $t^*$, both outputting the arm $m^*_{t^*}(i)$; its two Work modes start at $c_1+\delta_i$, $c_2+\delta_i$ and output at $o_1+\delta_i$, $o_2+\delta_i$, the same offsets from the root's outputs $o_j=c_j+J-1$, where $t^*<c_1<c_2$ are mature entries. Let $t_{\mathrm{cal}}=c_2+J+2(n-1)$ be the round when all players have entered Replay after the second outputs. At this round all replay lengths are equal, the realized matching equals $m^*_{t^*}$, and
--   $$
--   t^*\ <\ t_{\mathrm{cal}}\ \le\ \Psi_F^{\circ 3}(t^*+1).
--   $$
--   The paper states the lemma for $F=F_g$; its proof is written for every rule with (12).
--
--   Differences from the source:
--   - generalization: utilities μ_{i,k}, π_{k,i} ∈ [0,1] → arbitrary real utilities, injective in the second argument; reason: only the strict rankings enter the protocol and the POSM; every [0,1]-valued instance is an instance here
--   - encoding: players with entry b_i ≥ 1 and departure d_i ≤ ∞, finitely many arrivals and departures → a finite type ι of all players ever active, d_i ∈ ℕ∞ with ⊤ for ∞; reason: finiteness of ι is exactly finitely many arrivals and departures; each player enters once
--   - encoding: Algorithm 1 leaves q and blockOK uninitialized → initial values q = 0, blockOK = true; reason: both are written before they are read (q at every output, blockOK at every Sweep entry), so no execution changes
--   - generalization: nondecreasing computable F : ℕ≥1 → ℕ≥1 with F(x) ≥ H + 2x → any monotone F : ℕ → ℕ with F(x) ≥ H + 2x for x ≥ 1; reason: no argument uses computability; F(0) is never evaluated (a − ℓ ≥ 1 at every output, p.14) and every rule of (12) extends monotonically by F(0) := F(1)
--   - encoding: M_t = m*_t → IsPOSM I t (M F I t); reason: strict rankings make the POSM unique, so the two agree
--   - encoding: players labeled 1, …, n by BUS preference, δ_i = 2(i − 1) → δ_i = 2 · busRank I c i, busRank = number of active players BUS prefers to i; reason: busRank is the label minus one
--   - generalization: protocol Π_g with F = F_g for a feasible g → any replay rule F with (12); reason: the proof (p.18) is for any such F ("Taking F = F_g proves Lemma 1") and F_g satisfies (12) (p.20)
--   - encoding: t_cal, the round when all active players have entered Replay after the second Work outputs → t_cal = c₂ + J + 2(n − 1), with every player in Replay at t_cal; reason: the last player outputs at o₂ + 2(n − 1) and enters Replay one round later (Lemma 5)
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Lemma 1, p.9; proof App. A.3, pp.17–18

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_Psi
import Definitions.Def_DecDynMatch_IsPOSM
import Definitions.Def_DecDynMatch_OutputsAt
import Definitions.Def_DecDynMatch_IsMatureEntry

namespace DecDynMatch

/-- **Lemma 1 (Recovery and Calibration), for every replay rule with (12).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), Lemma 1, p.9: "∀ feasible function g and instance I, in protocol Π_g, each active
player i in the final market finishes two consecutive Work modes, initiated after t* and
outputting the arm m*_{t*}(i). Player i's outputs have the same time offset from the root's
outputs. Let t_cal be the round when all active players have entered Replay after the second Work
outputs. At this round, the players' replay lengths are all equal, and the realized matching equals
m*_{t*}, with t* < t_cal ≤ Ψ_{F_g}^{∘3}(t* + 1)." The proof (App. A.3, p.18) is written for any
rule F with (12): "Taking F = F_g proves Lemma 1".

With `P = P_{t*}` nonempty (the standing assumption of §2.3, p.5), `n = |P|`,
`δᵢ = 2 * busRank I t* i`: there are mature entries `t* < c₁ < c₂` (root outputs
`oⱼ = cⱼ + J − 1`) such that every `i ∈ P` starts Work at `cⱼ + δᵢ` and outputs at `oⱼ + δᵢ`
(`j = 1, 2`), with no output in between, both output arms being `m*_{t*}(i)`; and at
`t_cal = c₂ + J + 2(n − 1)` every player is in Replay, all replay lengths are equal, the realized
matching is the POSM of `P_{t*}`, and `t* < t_cal ≤ Ψ_F^{∘3}(t* + 1)`.

**Formalization Note.** Stated for every replay rule `F` with (12) rather than for `F_g` with
`g` feasible: every such `F_g` satisfies (12) (App. A.5, p.20), so the statement specializes to
the printed one. -/
theorem lemma_1 {K : ℕ} {ι : Type*} [Fintype ι] (F : ℕ → ℕ) (hF : RuleOK K F)
    (I : Instance K ι) (hne : (active I (tstar I)).Nonempty) :
    ∃ c₁ c₂ : ℕ, tstar I < c₁ ∧ c₁ < c₂ ∧ IsMatureEntry F I c₁ ∧ IsMatureEntry F I c₂ ∧
      (∀ i ∈ active I (tstar I),
        EntersWork F I (c₁ + 2 * busRank I (tstar I) i) i ∧
        OutputsAt F I (c₁ + J K - 1 + 2 * busRank I (tstar I) i) i ∧
        EntersWork F I (c₂ + 2 * busRank I (tstar I) i) i ∧
        OutputsAt F I (c₂ + J K - 1 + 2 * busRank I (tstar I) i) i ∧
        NoOutputBetween F I i (c₁ + J K - 1 + 2 * busRank I (tstar I) i)
          (c₂ + J K - 1 + 2 * busRank I (tstar I) i) ∧
        ∀ m, IsPOSM I (tstar I) m →
          m i = some (prop F I (c₁ + J K - 1 + 2 * busRank I (tstar I) i) i) ∧
          m i = some (prop F I (c₂ + J K - 1 + 2 * busRank I (tstar I) i) i)) ∧
      tstar I < c₂ + J K + 2 * ((active I (tstar I)).card - 1) ∧
      c₂ + J K + 2 * ((active I (tstar I)).card - 1) ≤ (Psi K F)^[3] (tstar I + 1) ∧
      (∀ i ∈ active I (tstar I),
        (cur F I (c₂ + J K + 2 * ((active I (tstar I)).card - 1)) i).m = .replay) ∧
      (∀ i ∈ active I (tstar I), ∀ j ∈ active I (tstar I),
        replayLen (cur F I (c₂ + J K + 2 * ((active I (tstar I)).card - 1)) i) =
          replayLen (cur F I (c₂ + J K + 2 * ((active I (tstar I)).card - 1)) j)) ∧
      IsPOSM I (tstar I) (M F I (c₂ + J K + 2 * ((active I (tstar I)).card - 1))) := by sorry

end DecDynMatch
