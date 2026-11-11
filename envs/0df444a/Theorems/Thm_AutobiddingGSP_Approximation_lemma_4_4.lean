-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_lemma_4_4
-- name    : AutobiddingGSP.Approximation.lemma_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:27:32.071737+00:00
-- url     : https://prove2.me/theorems/c11000a6-78e8-4873-b99e-7d8fb74b2063
-- title:
--   Lemma 4.4 — the position layers output each group's position in σ_h
-- statement:
--   In the setting of Lemma 4.3, fix $h\in[Q]$ with $w_h>0$ and a fixed point of the position circuit of p. 16: $z_{h,t,r}\in H(\min\{u_h-F_{t,r-1},F_{t,r}-u_h\})$, $\mathrm{Idx}^{(0)}_{h,t}=\sigma_h(t)=\sum_rr\,z_{h,t,r}$ ($0$ for the first group) and $\mathrm{Idx}^{(k+1)}_{h,t}-\mathrm{Idx}^{(k)}_{h,t}\in H(\mathrm{Idx}^{(k)}_{h,t}+\tfrac12-\sigma_h(t+k+1))$. Then for every group $t$, the final output $\mathrm{Idx}_{h,t}$ (after $T-t$ layers) is the position of $g_t$ in the group order of $\sigma_h$.
--
--   Differences from the source:
--   - generalization: ρ_t computed by the circuit → arbitrary probability vectors ρ_t; reason: as in Lemma 4.3
--   - encoding: at the fixed point of the circuit → the gate relations of the selector and position layers as hypotheses on z and idx; reason: these are exactly the fixed-point relations of the gates involved
--   - encoding: group t (1-based) with T − t layers → group t (0-based) with T − 1 − t layers; positions 0-based; reason: Lean indexing
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Lemma 4.4, p. 16 (PDF 16)

import Mathlib
import Definitions.Def_AutobiddingGSP_Approximation_Insertion

namespace AutobiddingGSP.Approximation

/-- **Lemma 4.4** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], p. 16 (PDF 16)). In the setting of Lemma 4.3, fix `h ∈ [Q]` with `w_h > 0`
and a fixed point of the position circuit (p. 16): selectors
`z_{h,t,r} ∈ H(min{u_h − F_{t,r−1}, F_{t,r} − u_h})`, computed positions
`σ_h(t) = ∑_r r z_{h,t,r}` (and `0` for the first group), `Idx^{(0)}_{h,t} = σ_h(t)` and layers
`Idx^{(k+1)}_{h,t} − Idx^{(k)}_{h,t} ∈ H(Idx^{(k)}_{h,t} + 1/2 − σ_h(t + k + 1))`. Then the final
output `Idx_{h,t} = Idx^{(T−t)}_{h,t}` is the (0-based) position of `g_t` in the deterministic
allocation `σ_h`.

**Formalization Note** Groups are 0-based: group `t` has `T − 1 − t` layers and `idx t 0` is
`σ_h(t)`; the position of group `t` in `σ_h` is its index in `execute (quantileSeq ρ h)`. -/
theorem lemma_4_4 {T : ℕ} (hT : 2 ≤ T) (ρ : (t : Fin T) → Fin (t.val + 1) → ℝ)
    (hρ : ∀ t : Fin T, 1 ≤ t.val → (∀ r, 0 ≤ ρ t r) ∧ ∑ r, ρ t r = 1)
    (h : ℕ) (hh : h ∈ Finset.Icc 1 (couplingQ T)) (hw : 0 < weightW ρ h)
    (z : (t : Fin T) → Fin (t.val + 1) → ℝ)
    (hz : ∀ t : Fin T, 1 ≤ t.val → ∀ r : Fin (t.val + 1),
      z t r ∈ Hset (min (midU ρ h - cumF ρ t r.val) (cumF ρ t (r.val + 1) - midU ρ h)))
    (idx : Fin T → ℕ → ℝ)
    (h0 : ∀ t : Fin T, idx t 0 = if t.val = 0 then 0 else ∑ r : Fin (t.val + 1), (r.val : ℝ) * z t r)
    (hstep : ∀ (t : Fin T) (k : ℕ) (hk : t.val + k + 1 < T),
      idx t (k + 1) - idx t k ∈ Hset (idx t k + 1 / 2 - idx ⟨t.val + k + 1, hk⟩ 0)) :
    ∀ t : Fin T, idx t (T - 1 - t.val) = (((execute (quantileSeq ρ h)).idxOf t : ℕ) : ℝ) := by sorry

end AutobiddingGSP.Approximation
