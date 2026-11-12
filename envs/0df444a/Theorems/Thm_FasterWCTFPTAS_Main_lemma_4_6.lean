-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_lemma_4_6
-- name    : FasterWCTFPTAS.Main.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:56.934698+00:00
-- url     : https://prove2.me/theorems/5ff83f87-79bd-473f-816a-fce4911f79ae
-- title:
--   Lemma 4.6 — a relaxed δ/m-representative set for (T_i, U_i, W_{>i}) is a δ-representative set
-- statement:
--   Fix $m\ge2$ machines and a sorted instance with $p_j>0$, $w_j\ge0$. Let $i\in[n]$, $\delta\in(0,1)$, and $D\subseteq\mathrm{DP}_i$. If $\widetilde D\subseteq D$ is a relaxed $\delta/m$-representative set of $D$ for
--
--   $$
--   (A,B,X)=(T_i,\ U_i,\ W_{>i}),
--   $$
--
--   then $\widetilde D$ is a $\delta$-representative set of $D$ for $i$.
--
--   This connects the geometric notion of §3 with the scheduling notion of §4.
--
--   Differences from the source:
--   - reading: Definition 4.2: for every pair (π^S, θ^S) ∈ D there exists (π^S̃, θ^S̃) ∈ D̃ with cost(S̃ ∪ S′) ≤ cost(S ∪ S′) + δOPT → for every schedule S whose pair lies in D there is a schedule S̃ whose pair lies in D̃ with that inequality; reason: cost(S ∪ S′) depends on S only through (π^S, θ^S) (identity in the proof of Lemma 4.6), so both readings define the same notion
--   - encoding: OPT ≔ min over partitions processed in increasing index order of the sorted instance → OPT m p w, the minimum over all nonpreemptive schedules (assignment and any per-machine order); reason: on a sorted instance (a hypothesis here) the two minima coincide by Smith's rule, which §4 invokes
--   - generalization: §4: integer processing times p_j > 0 and integer weights w_j ≥ 0 → real p_j > 0 and real w_j ≥ 0; reason: §1 (p. 1) states the problem for real data; integer instances are a special case
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 14 (PDF p. 15), Lemma 4.6

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_DP

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Lemma 4.6, p. 14 (PDF 15): let `i ∈ [n]`, `δ ∈ (0, 1)` and `D ⊆ DP_i`. A relaxed
`δ/m`-representative set `Dt ⊆ D` of `D` for `(T_i, U_i, W_{>i})` is a `δ`-representative set of
`D` for `i`. Hypotheses also include §4's standing assumptions (`m ≥ 2`, `p_j > 0`, jobs sorted by
Smith's ratio). -/
theorem lemma_4_6 {m n : ℕ} (hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : Sorted p w) (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (D Dt : Set (Pt m)) (hD : D ⊆ DP m p w i)
    (hrel : IsRelaxedRep (δ / m) (T p i) (U p w i) (Wgt w i) Dt D) :
    IsRepSet m p w i δ Dt D := by sorry

end FasterWCTFPTAS.Main
