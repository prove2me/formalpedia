-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_observation_4_4
-- name    : FasterWCTFPTAS.Main.observation_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:50.239277+00:00
-- url     : https://prove2.me/theorems/39a7a476-092a-4e23-b05b-f718261a84d6
-- title:
--   Observation 4.4 — representative sets are transitive
-- statement:
--   Fix $m\ge2$ machines and a sorted instance with $p_j>0$, $w_j\ge0$. Let $i\in\{0,\dots,n\}$, $\delta,\delta'\ge0$ and $A,B,C\subseteq\mathrm{DP}_i$. If $A$ is a $\delta$-representative set of $B$ for $i$ and $B$ is a $\delta'$-representative set of $C$ for $i$, then
--
--   $$
--   A\ \text{is a}\ (\delta+\delta')\text{-representative set of}\ C\ \text{for}\ i.
--   $$
--
--   Errors of successive sparsification steps add up; this is how the FPTAS accumulates the total error $n\delta=\varepsilon$.
--
--   Differences from the source:
--   - generalization: i ∈ [n] and δ, δ′ ∈ (0, 1) (Definition 4.2) → i ∈ {0, …, n} and δ, δ′ ≥ 0; reason: specializes to the source's range; δ + δ′ may leave (0, 1), and the proof of Theorem 1.1 uses i = 0 and multiples iδ
--   - reading: Definition 4.2: for every pair (π^S, θ^S) ∈ D there exists (π^S̃, θ^S̃) ∈ D̃ with cost(S̃ ∪ S′) ≤ cost(S ∪ S′) + δOPT → for every schedule S whose pair lies in D there is a schedule S̃ whose pair lies in D̃ with that inequality; reason: cost(S ∪ S′) depends on S only through (π^S, θ^S) (identity in the proof of Lemma 4.6), so both readings define the same notion
--   - encoding: OPT ≔ min over partitions processed in increasing index order of the sorted instance → OPT m p w, the minimum over all nonpreemptive schedules (assignment and any per-machine order); reason: on a sorted instance (a hypothesis here) the two minima coincide by Smith's rule, which §4 invokes
--   - generalization: §4: integer processing times p_j > 0 and integer weights w_j ≥ 0 → real p_j > 0 and real w_j ≥ 0; reason: §1 (p. 1) states the problem for real data; integer instances are a special case
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 14 (PDF p. 15), Observation 4.4

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_DP

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Observation 4.4, p. 14 (PDF 15): transitivity. Let `i ≤ n` and `A, B, C ⊆ DP_i`. If `A` is a
`δ`-representative set of `B` for `i` and `B` is a `δ'`-representative set of `C` for `i`, then `A`
is a `(δ + δ')`-representative set of `C` for `i`. Stated for `i ∈ {0, …, n}` and all `δ, δ' ≥ 0`
(reading R7). -/
theorem observation_4_4 {m n : ℕ} (hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : Sorted p w) (i : ℕ) (hi : i ≤ n) (δ δ' : ℝ) (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (A B C : Set (Pt m)) (hA : A ⊆ DP m p w i) (hB : B ⊆ DP m p w i) (hC : C ⊆ DP m p w i)
    (hAB : IsRepSet m p w i δ A B) (hBC : IsRepSet m p w i δ' B C) :
    IsRepSet m p w i (δ + δ') A C := by sorry

end FasterWCTFPTAS.Main
