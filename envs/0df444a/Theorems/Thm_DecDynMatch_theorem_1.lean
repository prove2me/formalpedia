-- Prove2me | Theorems.Thm_DecDynMatch_theorem_1
-- name    : DecDynMatch.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:00:54.891517+00:00
-- url     : https://prove2.me/theorems/74c57067-3f46-4812-a7a1-f3ebd2568b66
-- title:
--   Theorem 1 — SC-DA has cumulative POSM mismatch $O(t^*+K^2\log T)$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $K\ge 2$, let $I$ be any dynamic matching instance on $K$ arms (finitely many players, arbitrary unannounced arrivals and departures with $|P_t|\le K$, strict preferences known to each agent), and let $T>H=4(K^2+5K+1)+4$. Then the Self-Calibrating Deferred Acceptance protocol satisfies
--   $$
--   D(T;I)=\sum_{t=1}^{T}\mathbf 1\{M_t\ne m^*_t\}\ \le\ C\,\bigl(t^*+K^2\log T\bigr),
--   $$
--   where $M_t$ is the realized matching of round $t$, $m^*_t$ the player-optimal stable matching of the active market, and $t^*$ the last population-event time.
--
--   Players see only their own accept/reject outcomes; they have no global clock, no roster and no messages. The bound says that after the last population change the protocol pays only a logarithmic number of mismatched rounds, improving the earlier $O(T^{1-1/K}(\log T)^{2/K})$.
--
--   Differences from the source:
--   - reading: D(T; I) = O(t* + K² log T) for every K ≥ 2, I, T > H → one constant C chosen before K, ι, I and T; reason: p.21: the bound has constants uniform in K, g, I, T; the stronger reading
--   - generalization: Wlog, I has a non-empty final market (p.5) → every instance, including P_{t*} = ∅ and ι empty; reason: the general statement specializes to the source's; p.20 covers the empty case
--   - generalization: utilities μ_{i,k}, π_{k,i} ∈ [0,1] → arbitrary real utilities, injective in the second argument; reason: only the strict rankings enter the protocol and the POSM; every [0,1]-valued instance is an instance here
--   - encoding: players with entry b_i ≥ 1 and departure d_i ≤ ∞, finitely many arrivals and departures → a finite type ι of all players ever active, d_i ∈ ℕ∞ with ⊤ for ∞; reason: finiteness of ι is exactly finitely many arrivals and departures; each player enters once
--   - encoding: Algorithm 1 leaves q and blockOK uninitialized → initial values q = 0, blockOK = true; reason: both are written before they are read (q at every output, blockOK at every Sweep entry), so no execution changes
--   - encoding: M_t = m*_t → IsPOSM I t (M F I t); reason: strict rankings make the POSM unique, so the two agree
--   - encoding: K ≥ 2 → a field of Instance K ι (no separate hypothesis); reason: every instance carries it, so quantifying over instances is quantifying over K ≥ 2
--   - encoding: log T → Real.log (natural logarithm), T > H ≥ 64 so log T > 0; reason: the base only changes C
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Theorem 1, p.8

import Mathlib
import Definitions.Def_DecDynMatch_RuleOK
import Definitions.Def_DecDynMatch_D

namespace DecDynMatch

universe u

/-- **Theorem 1 (Cumulative Mismatch of SC-DA).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912 (held version,
sha256 6a27277e…), Theorem 1, p.8: "In the known-preference setting, for every K ≥ 2, dynamic matching
instance I, and time horizon T > H, SC-DA satisfies D(T; I) = O(t* + K² log T)."

There is one absolute constant `C` such that for every number of arms `K` (an instance requires
`K ≥ 2`), every finite set of players `ι`, every dynamic matching instance `I` and every horizon
`T > H = 4(K² + 5K + 1) + 4`, the number of rounds `1 ≤ t ≤ T` in which the realized matching of
SC-DA is not the POSM of round `t` is at most `C (t* + K² log T)`.

**Formalization Note.** `O(·)` is read with a single constant chosen before `K`, the instance and
`T` (App. A.5, p.21: "the static bound has constants uniform in K, g, I, T"). `log` is the natural
logarithm. The final market may be empty. -/
theorem theorem_1 :
    ∃ C : ℝ, ∀ (K : ℕ) (ι : Type u) [Fintype ι] (I : Instance K ι) (T : ℕ), H K < T →
      (D (scdaRule K) I T : ℝ) ≤ C * ((tstar I : ℝ) + (K : ℝ) ^ 2 * Real.log T) := by sorry

end DecDynMatch
