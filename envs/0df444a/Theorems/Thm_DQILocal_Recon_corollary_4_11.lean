-- Prove2me | Theorems.Thm_DQILocal_Recon_corollary_4_11
-- name    : DQILocal.Recon.corollary_4_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:40.369962+00:00
-- url     : https://prove2.me/theorems/7032cabb-d5cc-481d-9b86-0d25fdb0c6e3
-- title:
--   Corollary 4.11 — binary duality: $1-P_t\ge\frac14\sigma_\beta^2\bar{\mathfrak m}_t^{2k}\ge\frac14\sigma_\beta^2\bar{\mathfrak m}_\infty^{2k}$, and the BPQM tree threshold is $\beta_d$
-- statement:
--   Let $q=2$, $f(z)=z$, $k,D\ge2$, and $\sigma_\beta=\tanh(\beta/2)$. For every $\beta\ge0$ and every $t$, the optimal error for the root of $\mathcal T_t$ satisfies
--
--   $$1-P_t\;\ge\;\tfrac14\sigma_\beta^2\,\bar{\mathfrak m}_t^{2k}\;\ge\;\tfrac14\sigma_\beta^2\,\bar{\mathfrak m}_\infty^{2k},\qquad\bar{\mathfrak m}_\infty=\lim_{t\to\infty}\bar{\mathfrak m}_t .$$
--
--   Moreover, the set of $\beta\ge0$ with non-reconstruction is an interval $[0,\beta_d)$ or $[0,\beta_d]$, and the tree threshold of BPQM equals $\beta_d$.
--
--   This makes the decoder–reconstruction duality quantitative for Max-$k$-XORSAT: the mean posterior bias of the primal root bounds the optimal tree error from below.
--
--   Differences from the source:
--   - encoding: m̄_∞ = lim_{t→∞} m̄_t → mbarInf = ⨅ t, m̄_t; reason: m̄_t is nonincreasing and bounded (p. 29), so the infimum is the limit
--   - encoding: f(z) = z on ℤ_2 → f z = z.val ∈ {0, 1}; reason: the representative of z
--   - reading: the tree threshold of BPQM → the supremum in [0, ∞] of the β ≥ 0 at which the success probability of depth-t BPQM for the root tends to 1, for every choice of symbol-node unitaries; reason: p. 20 defines the threshold as the largest β at which BPQM succeeds as the depth grows; defined from BPQM itself so that the clause is not definitional
--   - encoding: the intervals [0, β_d), [0, β_d] → {β ≥ 0 : ofReal β < β_d}, {β ≥ 0 : ofReal β ≤ β_d}; reason: β_d ∈ [0, ∞]; same sets
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Corollary 4.11, p. 29

import Mathlib
import Definitions.Def_DQILocal_Recon_Spectra
import Definitions.Def_DQILocal_Recon_SpectralRecursion
import Definitions.Def_DQILocal_Recon_Reconstruction
import Definitions.Def_DQILocal_Recon_BPQM

namespace DQILocal.Recon

open scoped BigOperators

/-- **Corollary 4.11 (Binary duality).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Corollary 4.11, p. 29.
"For `q = 2` and `f(z) = z`, the optimal error for the root of `T_t` satisfies
`1 - P_t ≥ (1/4) σ_β² m̄_t^{2k} ≥ (1/4) σ_β² m̄_∞^{2k}`, `m̄_∞ = lim_{t→∞} m̄_t`. Moreover, the set of
`β` with non-reconstruction is an interval `[0, β_d)` or `[0, β_d]`, and the tree threshold of BPQM
equals `β_d`."

Here `σ_β = tanh(β/2)` (p. 19), `m̄_t = E[M^{(t)}(0) - M^{(t)}(1)]` (§4.6).

**Formalization Note.** `f(z) = z` is `z ↦ z.val ∈ {0, 1}`. The inequalities hold for every `β ≥ 0`
and every `t`. The intervals are taken among `β ≥ 0` with `β_d ∈ [0, ∞]`. The tree threshold of
BPQM (`bpqmThreshold`) is defined from the success probability of depth-`t` BPQM, for every choice
of symbol-node unitaries, not from `P_t`. Standing assumptions `k ≥ 2`, `D ≥ 2` (§3.1). -/
theorem corollary_4_11 (k D : ℕ) (hk : 2 ≤ k) (hD : 2 ≤ D) :
    let f : ZMod 2 → ℝ := fun z => (z.val : ℝ)
    (∀ β : ℝ, 0 ≤ β → ∀ t : ℕ,
      (1 / 4) * Real.tanh (β / 2) ^ 2 * mbar k D 2 f β t ^ (2 * k) ≤ 1 - Pt k D 2 f β t ∧
      (1 / 4) * Real.tanh (β / 2) ^ 2 * mbarInf k D 2 f β ^ (2 * k) ≤
        (1 / 4) * Real.tanh (β / 2) ^ 2 * mbar k D 2 f β t ^ (2 * k)) ∧
    ({β : ℝ | 0 ≤ β ∧ NonRecon k D 2 f β} = {β : ℝ | 0 ≤ β ∧ ENNReal.ofReal β < betaD k D 2 f} ∨
      {β : ℝ | 0 ≤ β ∧ NonRecon k D 2 f β} =
        {β : ℝ | 0 ≤ β ∧ ENNReal.ofReal β ≤ betaD k D 2 f}) ∧
    bpqmThreshold k D 2 f = betaD k D 2 f := by sorry

end DQILocal.Recon
