-- Prove2me | Theorems.Thm_DenseMatching_IPM_lemma_4_5
-- name    : DenseMatching.IPM.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:40:55.058345+00:00
-- url     : https://prove2.me/theorems/78080a99-0bad-419c-bc1d-fbc092d81d05
-- title:
--   Lemma 4.5 — one step keeps ν̂ in the box deterministically and decreases the potential (Eq. (13)) with probability 1 − n⁻¹⁴
-- statement:
--   On $K_{n/2,n/2}$ ($n=2k\ge2^{20}$, $m=k^2$, $\eta=10^{-5}$, $\alpha=10^7$), assume the invariants of the method: $\nu\in(-1,1)^E$, $\psi(\nu)\le10^2m$, and representatives $\bar\nu$ with Equation (4). Let $\Delta\mu$ be the clipped direction of $\bar\nu$ (Definition 4.2), let $\tilde f,\tilde\nu\in\mathbb R^E$ with $\|\tilde f\|_2\le10^2\eta$, $\|\tilde\nu\|_2\le2\cdot10^2\eta$, and let $p$ be probabilities with $p^s_e\le p_e\le1$ ($p^s$ of Equation (10)). Every edge is sampled independently with probability $p_e$ (Equation (11)), giving the sampling error $\nu^\circ$; let $\delta=10^{-3}\eta/\sqrt m$ and let the new deviations $\hat\nu$ be given by Equation (12),
--   $$\hat\nu_e-\nu_e=\frac{(1+\nu_e/10)\Delta\mu_e-\nu^\circ_e+\delta(\nu_e+10)}{1-\delta}.$$
--   Then for every outcome of positive probability, $|\hat\nu_e-\nu_e|\le(1-|\nu_e|)/2$ for every $e$, so $\hat\nu\in(-1,1)^E$; and with probability at least $1-n^{-14}$,
--   $$\psi(\hat\nu)\le\psi(\nu)-\frac{|\Delta\mu|^\top|\psi'(\bar\nu)|}{2}+4\eta^2\sqrt m\le10^2m.\tag{13}$$
--   This is the drift step behind the iteration count of Lemma 4.8.
--
--   Differences from the source:
--   - encoding: the complete bipartite graph K_{n/2,n/2} of Section 4 with n ≥ 2^20 (p. 26), m = n²/4 → vertices Fin k ⊕ Fin k, edges Fin k × Fin k oriented L → R, n = 2k with 2^19 ≤ k, m = k²; reason: same instances; n is even on K_{n/2,n/2}
--   - reading: 'under the invariants of Figure 3' / 'of the IPM algorithm' → explicit hypotheses ν ∈ (−1,1)^E, ψ(ν) ≤ 10²m and Equation (4) for the representatives ν̄; reason: p. 25: 'A statement made under the invariants of the IPM algorithm assumes ψ(ν) ≤ 10²m and Equation (4)'; the other invariants of Figure 3 concern objects (r, anchors, x) that do not occur in the statement
--   - encoding: θ ∈ [0, ∞] with 1/θ := 0 at θ = ∞ → clipTheta in ℝ≥0∞, 1/θ = (θ⁻¹).toReal; reason: same values; θ > 0 always
--   - encoding: 'with probability 1 − n^{−14}' over the independent sampling of Equation (11) → sampleProb p (failure event) ≤ 1/n^14, the product-Bernoulli probability as an explicit finite sum; reason: same probability for p ∈ [0,1]^E
--   - reading: 'for the sampling errors of Equation (11)', defined for f̃, ν̃ as in Lemma 4.4 and probabilities p_e ≥ p^s_e (p. 31) → hypotheses ‖f̃‖₂ ≤ 10²η, ‖ν̃‖₂ ≤ 2·10²η and p^s_e ≤ p_e ≤ 1; reason: these are the conditions under which Equation (11) is defined on p. 31
--   - encoding: the first bullet, '|ν̂_e − ν_e| ≤ (1 − |ν_e|)/2 for every e', for every realization of the sampling → for every outcome ω of the coins with positive probability (no coin of an edge with p_e = 1 fails, none with p_e = 0 succeeds); reason: the realizations of Equation (11) are exactly these outcomes; on a probability-zero outcome an edge with p_e = 1 would be unsampled and carry ν°_e = −ν̃_e, which the residue intensity does not control
-- source:
--   Dai, Peng, Sleator, Stepin, Yang, Approaching Optimality for Dense Bipartite Matching, STOC 2027 submission (manuscript sha256 0bdeb447…), pp. 31–32, Lemma 4.5

import Mathlib
import Definitions.Def_DenseMatching_IPM_Tools
import Definitions.Def_DenseMatching_IPM_FlowLP

namespace DenseMatching.IPM

/-- Lemma 4.5 (p. 31). On `K_{n/2,n/2}` (`n = 2k ≥ 2^20`, `m = k²`), under the invariants of the
IPM (`ν ∈ (−1, 1)^E`, `ψ(ν) ≤ 10²m`, Equation (4)), let `f̃, ν̃` be as in Lemma 4.4, let the
probabilities satisfy `pˢ_e ≤ p_e ≤ 1`, let every edge be sampled independently with probability
`p_e` (Equation (11)), `δ = 10⁻³η/√m`, and let the new deviations `ν̂` be given by Equation (12).
Then for every outcome of positive probability (no coin lands against a probability `0` or `1`)
`|ν̂_e − ν_e| ≤ (1 − |ν_e|)/2` for every `e`, so `ν̂ ∈ (−1, 1)^E`; and with
probability at least `1 − n⁻¹⁴`, `ψ(ν̂) ≤ ψ(ν) − |Δμ|⊤|ψ′(ν̄)|/2 + 4η²√m ≤ 10²m`. -/
theorem lemma_4_5 (k : ℕ) (hk : 2 ^ 19 ≤ k) (ν νbar ft νt p : KE k → ℝ) (hν : ∀ e, |ν e| < 1)
    (hψ : potential ν ≤ 10 ^ 2 * (k : ℝ) ^ 2) (hrep : RepresentativesClose eta ν νbar)
    (hft : l2norm ft ≤ 10 ^ 2 * eta) (hνt : l2norm νt ≤ 2 * 10 ^ 2 * eta)
    (hp : ∀ e, sparsityIntensity (2 * k) eta alpha νbar ft νt e ≤ p e ∧ p e ≤ 1) :
    let m : ℝ := (k : ℝ) ^ 2
    let νhat : (KE k → Bool) → KE k → ℝ := fun ω =>
      newDeviation (shrink eta m) ν (clippedDir eta νbar) (samplingErrorNu ft νt p ω)
    (∀ ω : KE k → Bool, (∀ e, (if ω e then p e else 1 - p e) ≠ 0) →
        (∀ e, |νhat ω e - ν e| ≤ (1 - |ν e|) / 2) ∧ ∀ e, |νhat ω e| < 1) ∧
      sampleProb p (fun ω => ¬ (potential (νhat ω) ≤
          potential ν - descent eta νbar / 2 + 4 * eta ^ 2 * Real.sqrt m ∧
        potential ν - descent eta νbar / 2 + 4 * eta ^ 2 * Real.sqrt m ≤ 10 ^ 2 * m)) ≤
        1 / (2 * (k : ℝ)) ^ 14 := by sorry

end DenseMatching.IPM
