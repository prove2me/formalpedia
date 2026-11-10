-- Prove2me | Theorems.Thm_DQILocal_Recon_theorem_5_5
-- name    : DQILocal.Recon.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:57.371195+00:00
-- url     : https://prove2.me/theorems/afdb9aa5-295d-4b3a-afbe-05b640e95054
-- title:
--   Theorem 5.5 — typical tree projection: $\Pr[\mathrm{LT}_t(i)\wedge\mathrm{TP}_t(i)]=1-o(1)$ for $t\le(\frac12-\delta)\log_{(k-1)(D-1)}m$
-- statement:
--   Let $q\ge2$, $k\ge2$, $D\ge3$ and $k<D$. Let $\delta>0$ and let $t=t_m$ satisfy $t_m\le(\frac12-\delta)\log_{(k-1)(D-1)}m$. Then, for random $(k,D)$-regular instances over $\mathbb Z_q$ from the configuration model or from Gallager's ensemble, and for a uniformly random symbol $i$,
--
--   $$\Pr\bigl[\mathrm{LT}_{t_m}(i)\text{ and }\mathrm{TP}_{t_m}(i)\bigr]=1-o(1)\qquad(m\to\infty).$$
--
--   The limits are taken along the sizes at which each ensemble is defined: $D\mid km$ for the configuration model and $D\mid m$ for Gallager's ensemble.
--
--   So at almost all depths at which a typical neighbourhood is a tree, the rest of the code also imposes no constraint on it.
--
--   Differences from the source:
--   - reading: for t ≤ (1/2 − δ) log_{(k−1)(D−1)} m, Pr[…] = 1 − o(1) → for every sequence t_m with t_m ≤ (1/2 − δ) log_{(k−1)(D−1)} m, the probability tends to 1; reason: uniformity in t (equivalent to the supremum of the failure probability over all such t tending to 0) is the stronger reading of a single depth
--   - encoding: the configuration model (half-edge pairing conditioned on no multiple edges) → the uniform law on (k, D)-regular m × (km/D) 0/1 matrices; reason: each simple biregular labelled graph arises from exactly (k!)^m (D!)^n bijections; p. 3 states the same law
--   - encoding: the ensembles are defined when D ∣ km, resp. D ∣ m; uniformly random symbol → limits along atTop ⊓ 𝓟 {m | D ∣ km}, resp. {m | D ∣ m}; i uniform on Fin m independent of B; probabilities as counting ratios; reason: the ensembles exist only at those m; same probabilities
-- source:
--   Augustino et al., Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with Local Quantum Decoders, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 5.5, p. 32

import Mathlib
import Definitions.Def_DQILocal_Recon_LocalConditions
import Definitions.Def_DQILocal_Recon_Ensembles

namespace DQILocal.Recon

open scoped BigOperators
open Filter Topology

/-- **Theorem 5.5 (Typical tree projection).**
Augustino et al., *Tight Information-Theoretic Threshold for Decoded Quantum Interferometry with
Local Quantum Decoders*, STOC 2027 submission (manuscript sha256 c861b07d…), Theorem 5.5, p. 32.
"Let `q ≥ 2`, `k ≥ 2`, `D ≥ 3`, and `k < D`. Let `δ > 0` and `t ≤ (1/2 - δ) log_{(k-1)(D-1)} m`.
Then, for random `(k, D)`-regular instances over `ℤ_q` from the configuration model or from
Gallager's ensemble, and for a uniformly random symbol `i`, `Pr[LT_t(i) and TP_t(i)] = 1 - o(1)`."

**Formalization Note.** "For `t ≤ (1/2 - δ) log_{(k-1)(D-1)} m` … `= 1 - o(1)`" is read uniformly in
`t`: for **every** sequence `t_m` with `t_m ≤ (1/2 - δ) log_{(k-1)(D-1)} m` the probability tends to
one (equivalently, the supremum of the failure probability over all such `t` tends to zero). The
limits are taken along the `m` at which each ensemble is defined: `D ∣ km` for the configuration
model (`n = km/D` checks) and `D ∣ m` for Gallager's ensemble. -/
theorem theorem_5_5 (q : ℕ) [NeZero q] (hq : 2 ≤ q) (k D : ℕ) (hk : 2 ≤ k) (hD : 3 ≤ D)
    (hkD : k < D) (δ : ℝ) (hδ : 0 < δ) (t : ℕ → ℕ)
    (ht : ∀ m : ℕ, (t m : ℝ) ≤ (1 / 2 - δ) * Real.logb (((k : ℝ) - 1) * ((D : ℝ) - 1)) m) :
    Tendsto (fun m => configProb k D q (t m) m) (atTop ⊓ 𝓟 {m | D ∣ k * m}) (𝓝 1) ∧
    Tendsto (fun m => gallagerProb k D q (t m) m) (atTop ⊓ 𝓟 {m | D ∣ m}) (𝓝 1) := by sorry

end DQILocal.Recon
