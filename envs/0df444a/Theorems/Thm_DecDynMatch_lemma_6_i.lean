-- Prove2me | Theorems.Thm_DecDynMatch_lemma_6_i
-- name    : DecDynMatch.lemma_6_i
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:53.741456+00:00
-- url     : https://prove2.me/theorems/8ac29687-a109-446c-b981-436c3d424e2b
-- title:
--   Lemma 6 (i) — sweep isolation
-- statement:
--   Let $F$ be a replay rule with (12). Let player $z$ enter Sweep at round $b$. If $z$ remains in this Sweep visit through round $d$ and all its BUS proposals in $[b,d]$ are accepted, then in every round of $[b,d]$ every other active player is in Seek or Replay and schedules no Work entry.
--
--   No assumption is made on population events: the lemma applies even if players arrive or depart during the sweep. It bounds the recovery time, since a sweeping root blocks every competing Work entry.
--
--   Differences from the source:
--   - generalization: utilities μ_{i,k}, π_{k,i} ∈ [0,1] → arbitrary real utilities, injective in the second argument; reason: only the strict rankings enter the protocol and the POSM; every [0,1]-valued instance is an instance here
--   - encoding: players with entry b_i ≥ 1 and departure d_i ≤ ∞, finitely many arrivals and departures → a finite type ι of all players ever active, d_i ∈ ℕ∞ with ⊤ for ∞; reason: finiteness of ι is exactly finitely many arrivals and departures; each player enters once
--   - encoding: Algorithm 1 leaves q and blockOK uninitialized → initial values q = 0, blockOK = true; reason: both are written before they are read (q at every output, blockOK at every Sweep entry), so no execution changes
--   - generalization: nondecreasing computable F : ℕ≥1 → ℕ≥1 with F(x) ≥ H + 2x → any monotone F : ℕ → ℕ with F(x) ≥ H + 2x for x ≥ 1; reason: no argument uses computability; F(0) is never evaluated (a − ℓ ≥ 1 at every output, p.14) and every rule of (12) extends monotonically by F(0) := F(1)
--   - encoding: z enters Sweep at round b and remains in this visit through d → the sweep qualification of z fires at b, and z is active with round-start mode Sweep in every round of [b, d]; reason: Sweep is entered only by qualification and a visit is a maximal run of Sweep rounds
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Lemma 6 (i), p.16

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_OutputsAt

namespace DecDynMatch

/-- **Lemma 6 (i) (Sweep isolation).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), Lemma 6 (i), p.16: "Let player z enter Sweep at round b. (i) If z remains in this visit through
round d and all its BUS proposals in [b, d] are accepted, then throughout this interval, every
other active player is in Seek or Replay and schedules no Work entry."

Hypotheses: the sweep qualification of `z` fires at round `b₀` (the paper's `b`); `z` stays
active and in Sweep in every round of `[b₀, d₀]`; every BUS proposal of `z` in `[b₀, d₀]` is
accepted. Conclusion: in every round `t ∈ [b₀, d₀]`, every other active player has round-start
mode Seek or Replay, and its state after the round has no pending Work entry.

**Formalization Note.** No population hypothesis: the paper applies (i) "even if population events
occurred in the meantime" (p.18). -/
theorem lemma_6_i {K : ℕ} {ι : Type*} [Fintype ι] (F : ℕ → ℕ) (hF : RuleOK K F)
    (I : Instance K ι) (z : ι) (b₀ d₀ : ℕ)
    (hq : QualifiesAt F I b₀ z)
    (hstay : ∀ t, b₀ ≤ t → t ≤ d₀ → z ∈ active I t ∧ (cur F I t z).m = .sweep)
    (hbus : ∀ t, b₀ ≤ t → t ≤ d₀ → prop F I t z = bus I → Accepts F I t z) :
    ∀ t, b₀ ≤ t → t ≤ d₀ → ∀ j ∈ active I t, j ≠ z →
      ((cur F I t j).m = .seek ∨ (cur F I t j).m = .replay) ∧
      (post F I t j).ν ≠ some .work := by sorry

end DecDynMatch
