-- Prove2me | Theorems.Thm_DQILocal_Recon_proposition_4_9
-- name    : DQILocal.Recon.proposition_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:43.126268+00:00
-- url     : https://prove2.me/theorems/e2d407e4-af1b-47bd-bd20-2ee1d4345f02
-- title:
--   Proposition 4.9 — degradation: $p_{\beta'}=p_\beta*\kappa$ gives $P_t(\beta')\ge P_t(\beta)$; then non-reconstruction is $[0,\beta_d)$ or $[0,\beta_d]$
-- statement:
--   Let $q\ge2$, $f$ a cost, $k,D\ge2$.
--
--   1. Let $0\le\beta'<\beta$ and suppose there is a probability vector $\kappa$ on $\mathbb Z_q$ with $p_{\beta'}=p_\beta*\kappa$. Then $P_t(\beta')\ge P_t(\beta)$ for every $t$.
--   2. If such a $\kappa$ exists for every pair $0\le\beta'<\beta$, then the set of $\beta\ge0$ with non-reconstruction is
--   $$[0,\beta_d)\qquad\text{or}\qquad[0,\beta_d],$$
--   where $\beta_d\in[0,\infty]$ is the reconstruction threshold.
--
--   This gives conditions under which the inverse temperatures without reconstruction form an interval, so that $\beta_d$ is a genuine threshold.
--
--   Differences from the source:
--   - encoding: the intervals [0, β_d) and [0, β_d] with β_d ∈ [0, ∞] → {β ≥ 0 : ofReal β < β_d} and {β ≥ 0 : ofReal β ≤ β_d} with β_d in ENNReal; reason: [0, ∞) when β_d = ∞; same sets
--   - encoding: every pair β' < β → every pair 0 ≤ β' < β; reason: inverse temperatures range over [0, ∞) throughout (§3.1)
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Proposition 4.9, p. 28

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_SpectralRecursion
import Definitions.Def_DQILocal_Recon_Reconstruction

namespace DQILocal.Recon

open scoped BigOperators

/-- **Proposition 4.9 (Degradation).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Proposition 4.9, p. 28.
"Let `0 ≤ β' < β`, and suppose that there is a probability vector `κ` on `ℤ_q` with
`p_{β'} = p_β ∗ κ`. Then `P_t(β') ≥ P_t(β)` for every `t`. If such a `κ` exists for every pair
`β' < β`, then the set of `β` with non-reconstruction is `[0, β_d)` or `[0, β_d]`."

**Formalization Note.** `β_d ∈ [0, ∞]` (Definition 4.8); the intervals are written with
`ENNReal.ofReal β < β_d` and `ENNReal.ofReal β ≤ β_d` among `β ≥ 0`, so `[0, β_d)` with `β_d = ∞` is
`[0, ∞)`. "Every pair `β' < β`" ranges over `0 ≤ β' < β`. Standing assumptions `q ≥ 2`, `k ≥ 2`,
`D ≥ 2` (§3.1). -/
theorem proposition_4_9 (q : ℕ) [NeZero q] (hq : 2 ≤ q) (f : ZMod q → ℝ) (k D : ℕ) (hk : 2 ≤ k)
    (hD : 2 ≤ D) :
    (∀ β' β : ℝ, 0 ≤ β' → β' < β → ∀ κ : ZMod q → ℝ, IsProbVec κ →
      gibbsWeight q f β' = conv (gibbsWeight q f β) κ →
        ∀ t : ℕ, Pt k D q f β t ≤ Pt k D q f β' t) ∧
    ((∀ β' β : ℝ, 0 ≤ β' → β' < β →
        ∃ κ : ZMod q → ℝ, IsProbVec κ ∧ gibbsWeight q f β' = conv (gibbsWeight q f β) κ) →
      {β : ℝ | 0 ≤ β ∧ NonRecon k D q f β} =
          {β : ℝ | 0 ≤ β ∧ ENNReal.ofReal β < betaD k D q f} ∨
        {β : ℝ | 0 ≤ β ∧ NonRecon k D q f β} =
          {β : ℝ | 0 ≤ β ∧ ENNReal.ofReal β ≤ betaD k D q f}) := by sorry

end DQILocal.Recon
