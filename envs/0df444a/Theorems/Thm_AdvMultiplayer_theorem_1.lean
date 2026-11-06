-- Prove2me | Theorems.Thm_AdvMultiplayer_theorem_1
-- name    : AdvMultiplayer.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:11:30.577973+00:00
-- url     : https://prove2.me/theorems/a528e9d6-6f92-43d4-a7b2-6b521ab4e037
-- title:
--   Theorem 1 — main result: $R_T(r)\le Cm^{3/2}\sqrt{KT}b_N^2$
-- statement:
--   There is an absolute constant $C$ such that, for all integers $2\le m<K$ and $T\ge1$, there exist a table and a strategy profile in model (1) such that, for every reward matrix $r\in[0,1]^{T\times K}$, including matrices chosen with knowledge of the table,
--   $$R_T(r)\le Cm^{3/2}\sqrt{KT}\,b_N^2.$$
--   Moreover, a table sampled from an explicit distribution has this property with probability at least $1-O(1/N)$. Sampling the table and executing the strategy take polynomially many operations in $K,m,T$, in the exact-arithmetic model of Section 8.
--
--   Here $N=2Km(T+1)$ and $b_N=\lceil\log_2(N+1)\rceil$. No collision information, shared randomness or communication channel is available to the players. The theorem refutes the conjectured $\Omega(T^{2/3})$ lower bound for two players without collision information.
--
--   Differences from the source:
--   - reading: there exist a table and a strategy profile; an explicit distribution → the strategy is `protocol`, the distribution is `tableLaw` of Algorithm 9; reason: the sampled-table and cost clauses have content only for these objects; this implies the existential form
--   - reading: probability at least 1 - O(1/N) → the outer measure of the bad tables is at most C′/N, with one absolute C′; reason: stays honest if the bad set is not measurable
--   - reading: polynomially many operations in the exact-arithmetic model → ticks at most c(KmT)^c, with the floor charged as a ticked search; reason: Section 8 does not list the floor; a unit-cost floor would be the weaker reading
--   - generalization: execution cost, for a sampled table → the bound for every table in the table type, every r and all tapes; reason: it specializes to the sampled table; Prop. 23 says the loops have these limits on wrong inputs
--   - encoding: private randomness → a tape of Unif([0,1)) coordinates per player, independent across players; reason: the unit-cost draws of Section 8
--   - encoding: the expectation in (2) → the property of a table includes measurability of the play in the tapes; reason: so that the expectation is meaningful
-- source:
--   Gan, Square-Root Regret for Adversarial Multiplayer Bandits without Collision Information or Shared Randomness, arXiv:2610.05688, Theorem 1, p.4, (3)

import Mathlib
import Definitions.Def_AdvMultiplayer_Execution

open MeasureTheory

namespace AdvMultiplayer

/-- **Theorem 1 (main result).** Gan, *Square-Root Regret for Adversarial Multiplayer Bandits without
Collision Information or Shared Randomness*, arXiv:2610.05688, Theorem 1, p.4, (3). There is an absolute
constant `C` such that, for all integers `2 ≤ m < K` and `T ≥ 1`, there exist a table and a strategy
profile in model (1) with `R_T(r) ≤ C m^{3/2} √(KT) b_N²` for every reward matrix `r ∈ [0,1]^{T×K}`,
including matrices chosen with knowledge of the table. Moreover a table sampled from an explicit
distribution has this property with probability at least `1 - O(1/N)`. Sampling the table and executing
the strategy take polynomially many operations in `K, m, T`.

**Formalization Note.** The strategy profile is `protocol` and the distribution is `tableLaw` (Algorithm
9), for which the "Moreover" clauses have content. A table is good if the play is measurable in the tapes
and (3) holds for every `r`, with `r` quantified after the table. The sampled-table clause bounds the
outer measure of the bad tables by `C'/N`. Operations are ticks. `Size` carries `2 ≤ m < K`, `1 ≤ T`. -/
theorem theorem_1 : ∃ (C C' : ℝ) (c : ℕ), 0 < C ∧ 0 < C' ∧ ∀ p : Size,
    (∃ tab : Table p,
      (∀ r : Rewards p, IsRewards p r → ∀ t i,
        Measurable fun ω => armAt p (protocol p tab) r ω t i) ∧
      ∀ r : Rewards p, IsRewards p r → regret p (protocol p tab) r ≤
        C * (p.m : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt ((p.K : ℝ) * p.T) * (p.bN : ℝ) ^ 2) ∧
    tableLaw p {tab : Table p | ¬ (
      (∀ r : Rewards p, IsRewards p r → ∀ t i,
        Measurable fun ω => armAt p (protocol p tab) r ω t i) ∧
      ∀ r : Rewards p, IsRewards p r → regret p (protocol p tab) r ≤
        C * (p.m : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt ((p.K : ℝ) * p.T) * (p.bN : ℝ) ^ 2)}
      ≤ ENNReal.ofReal (C' / (p.N : ℝ)) ∧
    Measurable (sampledTable p) ∧
    (tableTapeLaw p).map (sampledTable p) = tableLaw p ∧
    (∀ ω : TableTape p, sampleTicks p ω ≤ c * (p.K * p.m * p.T) ^ c) ∧
    ∀ (tab : Table p) (r : Rewards p) (ω : Tapes p),
      playTicks p tab r ω ≤ c * (p.K * p.m * p.T) ^ c := by sorry

end AdvMultiplayer
