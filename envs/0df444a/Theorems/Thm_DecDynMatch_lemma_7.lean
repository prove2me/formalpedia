-- Prove2me | Theorems.Thm_DecDynMatch_lemma_7
-- name    : DecDynMatch.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:52.08968+00:00
-- url     : https://prove2.me/theorems/44591cb4-c01f-4281-a722-a9d09af29a46
-- title:
--   Lemma 7 — recovery to consecutive mature outputs
-- statement:
--   Let $F$ be a replay rule with (12) and let $I$ be an instance with nonempty final market $P=P_{t^*}$, $n=|P|$, players labeled by BUS preference. Then there are two mature executions beginning after $t^*$, at entries $t^*<c_1<c_2$ with root outputs $o_j=c_j+J-1$, such that every player outputs at $o_1+\delta_i$ and $o_2+\delta_i$, these two outputs are consecutive in its output history (so the second output uses the local time of the first as its old $\ell$), and, with $t_{\mathrm{cal}}=c_2+J+2(n-1)$ the round when all players have entered Replay after the second outputs,
--   $$
--   t_{\mathrm{cal}}\ \le\ \Psi_F^{\circ 3}(t^*+1). \tag{20}
--   $$
--
--   Differences from the source:
--   - generalization: utilities μ_{i,k}, π_{k,i} ∈ [0,1] → arbitrary real utilities, injective in the second argument; reason: only the strict rankings enter the protocol and the POSM; every [0,1]-valued instance is an instance here
--   - encoding: players with entry b_i ≥ 1 and departure d_i ≤ ∞, finitely many arrivals and departures → a finite type ι of all players ever active, d_i ∈ ℕ∞ with ⊤ for ∞; reason: finiteness of ι is exactly finitely many arrivals and departures; each player enters once
--   - encoding: Algorithm 1 leaves q and blockOK uninitialized → initial values q = 0, blockOK = true; reason: both are written before they are read (q at every output, blockOK at every Sweep entry), so no execution changes
--   - generalization: nondecreasing computable F : ℕ≥1 → ℕ≥1 with F(x) ≥ H + 2x → any monotone F : ℕ → ℕ with F(x) ≥ H + 2x for x ≥ 1; reason: no argument uses computability; F(0) is never evaluated (a − ℓ ≥ 1 at every output, p.14) and every rule of (12) extends monotonically by F(0) := F(1)
--   - encoding: players labeled 1, …, n by BUS preference, δ_i = 2(i − 1) → δ_i = 2 · busRank I c i, busRank = number of active players BUS prefers to i; reason: busRank is the label minus one
--   - encoding: t_cal, the round when all players have entered Replay after the second outputs → t_cal = c₂ + J + 2(n − 1), with every player in Replay at t_cal; reason: the last player outputs at o₂ + 2(n − 1) and enters Replay one round later (Lemma 5)
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Lemma 7, p.17

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_Psi
import Definitions.Def_DecDynMatch_OutputsAt
import Definitions.Def_DecDynMatch_IsMatureEntry

namespace DecDynMatch

/-- **Lemma 7 (Recovery to actual consecutive mature outputs).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), Lemma 7, p.17: "For every dynamic matching instance I with a nonempty final
market, run Algorithm 1 from its prescribed initialization with the update Equation (13). There
are two mature executions beginning after t*. Let t_cal be the round when all players have entered
Replay after the second execution's outputs. Then t_cal ≤ Ψ_F^{∘3}(t* + 1). (20) Each player's two
outputs are consecutive in its actual output history, so the second output uses the local time of
the first output as its old ℓ."

With `P = P_{t*}` (the final market, assumed nonempty), `n = |P|`, `δᵢ = 2 * busRank I t* i`:
there are mature entries `t* < c₁ < c₂` (root outputs `oⱼ = cⱼ + J − 1`) such that every
`i ∈ P` outputs at `o₁ + δᵢ` and `o₂ + δᵢ` with no output in between, the `ℓ` held at the second
output is the local time of the first, every player is in Replay at
`t_cal = c₂ + J + 2(n − 1)` (the round the last player enters Replay after its second output), and
`t_cal ≤ Ψ_F^{∘3}(t* + 1)`. -/
theorem lemma_7 {K : ℕ} {ι : Type*} [Fintype ι] (F : ℕ → ℕ) (hF : RuleOK K F)
    (I : Instance K ι) (hne : (active I (tstar I)).Nonempty) :
    ∃ c₁ c₂ : ℕ, tstar I < c₁ ∧ c₁ < c₂ ∧ IsMatureEntry F I c₁ ∧ IsMatureEntry F I c₂ ∧
      (∀ i ∈ active I (tstar I),
        OutputsAt F I (c₁ + J K - 1 + 2 * busRank I (tstar I) i) i ∧
        OutputsAt F I (c₂ + J K - 1 + 2 * busRank I (tstar I) i) i ∧
        NoOutputBetween F I i (c₁ + J K - 1 + 2 * busRank I (tstar I) i)
          (c₂ + J K - 1 + 2 * busRank I (tstar I) i) ∧
        (cur F I (c₂ + J K - 1 + 2 * busRank I (tstar I) i) i).l =
          (cur F I (c₁ + J K - 1 + 2 * busRank I (tstar I) i) i).a) ∧
      (∀ i ∈ active I (tstar I),
        (cur F I (c₂ + J K + 2 * ((active I (tstar I)).card - 1)) i).m = .replay) ∧
      c₂ + J K + 2 * ((active I (tstar I)).card - 1) ≤ (Psi K F)^[3] (tstar I + 1) := by sorry

end DecDynMatch
