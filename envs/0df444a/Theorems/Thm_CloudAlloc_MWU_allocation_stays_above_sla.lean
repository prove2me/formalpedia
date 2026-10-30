-- Prove2me | Theorems.Thm_CloudAlloc_MWU_allocation_stays_above_sla
-- name    : CloudAlloc.MWU.allocation_stays_above_sla
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:45:20.184877+00:00
-- url     : https://prove2.me/theorems/3ab2c359-a8ba-4446-abc3-088efa46f9e7
-- title:
--   Proof of Theorem 4: a busy user's allocation never goes below $(1-\varepsilon c)(1-\varepsilon)\beta(i)$
-- statement:
--   Let $N\ge 2$, $0<\varepsilon\le 1/10$, $0<\eta\le 1/3$, SLAs $\beta\ge 0$ with $\sum_i\beta(i)\le 1$, nonnegative loads, $h$ a run of Algorithm 1, and $c=\varepsilon\eta/(4N)$. If user $i$ has $h_{\tau^\star}(i)\ge(1-\varepsilon)\beta(i)$ and its queue is non-empty at every time $\tau$ with $\tau^\star\le\tau<t'$, then
--
--   $$
--   h_{t'}(i)\ \ge\ (1-\varepsilon c)(1-\varepsilon)\beta(i).
--   $$
--
--   This is the step of the proof of Theorem 4 that, once a busy user reaches $(1-\varepsilon)\beta(i)$, keeps it there.
--
--   Differences from the source:
--   - reading: never go below … for all τ ≥ τ⋆ → for all t′ ≥ τ⋆ such that user i's queue is non-empty on [τ⋆, t′); reason: the proof's standing assumption is that i's queue is non-empty; unrestricted the claim is false, since an idle user decays to ε/N < (1 − εc)(1 − ε)·2ε/N
--   - generalization: w_{τ⋆}(i) ≥ (1 − ε)β(i) → h_{τ⋆}(i) ≥ (1 − ε)β(i); reason: w ≤ h, so the printed hypothesis implies this one
--   - generalization: η in Algorithm 1's input range 0 < η < 1/3 (no η range printed in this statement) → 0 < η ≤ 1/3; reason: the range printed in Lemma 2 and Theorem 4; it contains Algorithm 1's input range, so the statement specializes to it
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, proof of Theorem 4, p. 13 (unnumbered)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run

namespace CloudAlloc.MWU

/-- **"Never go below": an active user's allocation stays above `(1 − εc)(1 − ε)β(i)`.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, proof of Theorem 4, p. 13 (unnumbered):
"From the previous analysis we obtain the existence of `τ⋆ ∈ [t, t + p̃]` such that
`wτ⋆(i) ≥ (1−ε)β(i)`. By using Lemmas 1 and 2, we can show that the allocation `hτ(i)` will never go
below `(1−εc)(1 − ε)β(i)` for all `τ ≥ τ⋆`."

For a run of Algorithm 1 (standing hypotheses, `0 < η ≤ 1/3`) and `c = εη/(4N)`: if user `i`'s
allocation is at least `(1 − ε)β(i)` at time `τ⋆` and its queue is non-empty at every time from `τ⋆`
on, then its allocation is at least `(1 − εc)(1 − ε)β(i)` at every later time.

**Formalization Note.** Lean time `t` is the paper's `t + 1`; `ts` is `τ⋆`. "For all `τ ≥ τ⋆`" is read
under the proof's standing assumption that user `i`'s queue is non-empty throughout (the window
`[τ⋆, t′)` here): without it the claim is false, since an idle user decays to `ε/N`, below
`(1 − εc)(1 − ε)·2ε/N`. The hypothesis is placed on the allocation `h_{τ⋆}(i)` rather than on the work
`w_{τ⋆}(i)`; since `w ≤ h`, this covers the printed case. -/
theorem allocation_stays_above_sla {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ0 : ∀ i, 0 ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    let c := ε * η / (4 * (N : ℝ))
    ∀ (i : Fin N) (ts t' : ℕ), ts ≤ t' → (1 - ε) * β i ≤ h ts i →
      (∀ τ, ts ≤ τ → τ < t' → 0 < queue h L τ i) → (1 - ε * c) * (1 - ε) * β i ≤ h t' i := by sorry

end CloudAlloc.MWU
