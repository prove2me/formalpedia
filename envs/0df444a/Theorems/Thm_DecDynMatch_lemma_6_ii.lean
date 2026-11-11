-- Prove2me | Theorems.Thm_DecDynMatch_lemma_6_ii
-- name    : DecDynMatch.lemma_6_ii
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:18.094784+00:00
-- url     : https://prove2.me/theorems/a005cc43-2751-44e0-9c25-ac6d14b1f9ca
-- title:
--   Lemma 6 (ii) — a successful sweep gives a mature entry
-- statement:
--   Let $F$ be a replay rule with (12). Let player $z$ enter Sweep at round $b$. If this visit completes an all-accepted block at round $e$ and no population event occurs at $e+1$, then $e+1$ is a mature entry with root $z$.
--
--   Differences from the source:
--   - generalization: utilities μ_{i,k}, π_{k,i} ∈ [0,1] → arbitrary real utilities, injective in the second argument; reason: only the strict rankings enter the protocol and the POSM; every [0,1]-valued instance is an instance here
--   - encoding: players with entry b_i ≥ 1 and departure d_i ≤ ∞, finitely many arrivals and departures → a finite type ι of all players ever active, d_i ∈ ℕ∞ with ⊤ for ∞; reason: finiteness of ι is exactly finitely many arrivals and departures; each player enters once
--   - encoding: Algorithm 1 leaves q and blockOK uninitialized → initial values q = 0, blockOK = true; reason: both are written before they are read (q at every output, blockOK at every Sweep entry), so no execution changes
--   - generalization: nondecreasing computable F : ℕ≥1 → ℕ≥1 with F(x) ≥ H + 2x → any monotone F : ℕ → ℕ with F(x) ≥ H + 2x for x ≥ 1; reason: no argument uses computability; F(0) is never evaluated (a − ℓ ≥ 1 at every output, p.14) and every rule of (12) extends monotonically by F(0) := F(1)
--   - encoding: the visit completes an all-accepted block at round e → z stays in Sweep from b through e and its Sweep feedback at e schedules Work; reason: in Sweep, Work is scheduled exactly when a block of 2K proposals completes with every proposal accepted
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Lemma 6 (ii), p.16

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_OutputsAt
import Definitions.Def_DecDynMatch_IsMatureEntry

namespace DecDynMatch

/-- **Lemma 6 (ii) (Mature entry after a successful sweep).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), Lemma 6 (ii), p.16: "Let player z enter Sweep at round b. … (ii) If this visit completes an
all-accepted block at round e and no population event occurs at e + 1, then e + 1 is a mature
entry with root z."

Hypotheses: the sweep qualification of `z` fires at `b₀`; `z` stays active and in Sweep through
`e`; at round `e` its Sweep feedback schedules Work (which in Sweep happens exactly when a block
completes with every proposal accepted); round `e + 1` has no population event. Conclusion:
`e + 1` is a mature entry with root `z`. -/
theorem lemma_6_ii {K : ℕ} {ι : Type*} [Fintype ι] (F : ℕ → ℕ) (hF : RuleOK K F)
    (I : Instance K ι) (z : ι) (b₀ e : ℕ)
    (hq : QualifiesAt F I b₀ z)
    (hstay : ∀ t, b₀ ≤ t → t ≤ e → z ∈ active I t ∧ (cur F I t z).m = .sweep)
    (hblock : (post F I e z).ν = some .work)
    (hev : ¬ IsEvent I (e + 1)) :
    IsMatureEntryWithRoot F I (e + 1) z := by sorry

end DecDynMatch
