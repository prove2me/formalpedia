-- Prove2me | Theorems.Thm_FTConnOracle_Main_fact_4_1
-- name    : FTConnOracle.Main.fact_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:32:36.022733+00:00
-- url     : https://prove2.me/theorems/5e8612fc-e16a-45d7-b7f4-f2d7501f8d85
-- title:
--   Fact 4.1 — disjoint nonempty sets with equal expander neighbourhoods have more than t elements each
-- statement:
--   Let $n\ge2$ and let $B$ be a bipartite graph with left side $[n]$ and right side $[r]$, all of whose left vertices have degree $\ell\ge1$, satisfying (4.1) for the parameter $t$. Let $X,Y\subseteq[n]$ be nonempty disjoint sets. Then
--
--   $$\Gamma(X)=\Gamma(Y)\ \Longrightarrow\ |X|>t\ \text{ and }\ |Y|>t.$$
--
--   This is the expansion fact behind local amplification (Lemma 4.2(b)).
--
--   Differences from the source:
--   - generalization: the bipartite graph B fixed by Lemma 4.1 for n and an integer 1 ≤ t < n/4 (right side r = O(t log(2n)), left degree ℓ = O(log(2n))) → every B with left side [n], any right side [r], all left degrees equal to some ℓ ≥ 1 and property (4.1) for the parameter t, for every t ∈ ℕ; reason: the proof uses only left-regularity with ℓ ≥ 1 and (4.1); Lemma 4.1's B is one such graph, so the statement specializes to the source's
-- source:
--   Parter, Tzalik, Deterministic Fault-Tolerant Connectivity Oracles with Subqadratic Space, STOC 2027 submission (manuscript sha256 168306b7…), p. 16 (PDF 18), Fact 4.1

import Mathlib
import Definitions.Def_FTConnOracle_Main_Expander

namespace FTConnOracle.Main

/-- Fact 4.1 (p. 16): let `B` have all left degrees equal to `ℓ ≥ 1` and satisfy (4.1) for `t`.
If `X, Y ⊆ [n]` are nonempty disjoint sets with `Γ(X) = Γ(Y)`, then `|X| > t` and `|Y| > t`. -/
theorem fact_4_1 {n r ℓ t : ℕ} (hn : 2 ≤ n) (B : Fin n → Finset (Fin r))
    (hB : IsLosslessExpander B ℓ t) (X Y : Finset (Fin n)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hXY : Disjoint X Y) (hΓ : nbhd B X = nbhd B Y) :
    t < X.card ∧ t < Y.card := by sorry

end FTConnOracle.Main
