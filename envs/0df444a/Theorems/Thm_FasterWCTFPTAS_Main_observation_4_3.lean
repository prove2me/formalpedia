-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_observation_4_3
-- name    : FasterWCTFPTAS.Main.observation_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:07:42.743969+00:00
-- url     : https://prove2.me/theorems/824d315a-dc00-4870-8bd9-871aae3750c9
-- title:
--   Observation 4.3 — representative sets pass through the recurrence
-- statement:
--   Fix $m\ge2$ machines and a sorted instance with $p_j>0$, $w_j\ge0$. Let $i\in[n]$ and $\delta\ge0$. If $\widetilde{\mathrm{DP}}_{i-1}$ is a $\delta$-representative set of $\mathrm{DP}_{i-1}$ for $i-1$, then
--
--   $$
--   \widehat{\mathrm{DP}}_i=\{(\pi+e_kp_i,\ \theta+w_i(\pi_k+p_i)):(\pi,\theta)\in\widetilde{\mathrm{DP}}_{i-1},\ k\in[m-1]\}\cup\{(\pi,\ \theta+w_i(T_{i-1}-\|\pi\|_1+p_i)):(\pi,\theta)\in\widetilde{\mathrm{DP}}_{i-1}\}
--   $$
--
--   is a $\delta$-representative set of $\mathrm{DP}_i$ for $i$.
--
--   Together with Observation 4.4 this shows by induction that the sets kept by the FPTAS are $i\delta$-representative.
--
--   **Formalization Note** The job `i : Fin n` is the paper's job $i+1$.
--
--   Differences from the source:
--   - encoding: jobs 1, …, n and i ∈ [n] → jobs Fin n indexed from 0; the job i : Fin n is the paper's job i + 1, so the statement is about DP_{i+1} and DP_i; reason: index shift only; T p i is the paper's T_{(i+1)−1}
--   - generalization: δ ∈ (0, 1) (Definition 4.2) → every δ ≥ 0; reason: specializes to δ ∈ (0, 1); the proof of Theorem 1.1 applies the observation with (i − 1)δ, which is 0 at i = 1
--   - reading: Definition 4.2: for every pair (π^S, θ^S) ∈ D there exists (π^S̃, θ^S̃) ∈ D̃ with cost(S̃ ∪ S′) ≤ cost(S ∪ S′) + δOPT → for every schedule S whose pair lies in D there is a schedule S̃ whose pair lies in D̃ with that inequality; reason: cost(S ∪ S′) depends on S only through (π^S, θ^S) (identity in the proof of Lemma 4.6), so both readings define the same notion
--   - encoding: OPT ≔ min over partitions processed in increasing index order of the sorted instance → OPT m p w, the minimum over all nonpreemptive schedules (assignment and any per-machine order); reason: on a sorted instance (a hypothesis here) the two minima coincide by Smith's rule, which §4 invokes
--   - generalization: §4: integer processing times p_j > 0 and integer weights w_j ≥ 0 → real p_j > 0 and real w_j ≥ 0; reason: §1 (p. 1) states the problem for real data; integer instances are a special case
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 13 (PDF p. 14), Observation 4.3

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_DP

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Observation 4.3, p. 13 (PDF 14): representativeness passes through the recurrence. For the
job `i : Fin n` (the paper's job `i + 1`), if `DPt` is a `δ`-representative set of `DP_i` for `i`,
then `recur_i(DPt)` is a `δ`-representative set of `DP_{i+1}` for `i + 1`. Stated for every
`δ ≥ 0` (reading R7; the paper's `δ ∈ (0,1)` is a special case). -/
theorem observation_4_3 {m n : ℕ} (hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : Sorted p w) (i : Fin n) (δ : ℝ) (hδ : 0 ≤ δ) (DPt : Set (Pt m))
    (hrep : IsRepSet m p w i.val δ DPt (DP m p w i.val)) :
    IsRepSet m p w (i.val + 1) δ (recur m p w i DPt) (DP m p w (i.val + 1)) := by sorry

end FasterWCTFPTAS.Main
