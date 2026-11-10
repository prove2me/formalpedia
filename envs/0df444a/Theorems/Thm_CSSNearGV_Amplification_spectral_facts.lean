-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_spectral_facts
-- name    : CSSNearGV.Amplification.spectral_facts
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:22.045669+00:00
-- url     : https://prove2.me/theorems/acc524be-680c-4691-a604-274437eec59a
-- title:
--   Proposition 3.7 — spectral shape symmetry and monotonicity
-- statement:
--   For every $m\ge0$, $r_A^{(m)}$ is nonnegative, symmetric about $1/2$, and nondecreasing on $[0,1/2]$. Its difference from binary entropy is symmetric and nonincreasing there. Moreover,
--   $$r_A^{(m)}(\gamma)\le r_A^{(m-1)}(\gamma),\qquad\delta^{(m)}\ge\delta^{(m-1)}\quad(m\ge1).$$
--   The feasible maximum defining each update is attained, and the zero interval has greatest element $\delta^{(m)}$, as required by Definition 3.4.
--
--   These facts justify the threshold representation and the comparison estimates.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - reading: increasing and decreasing → nondecreasing and nonincreasing; reason: the spectral shapes have zero plateaus, as used explicitly in the paper
--   - encoding: maxima and inverse-entropy root used in Definitions 1.2 and 3.2–3.4 → supremum/infimum definitions with attainment and the root property included as conclusions; reason: well-posedness is proved rather than assumed or silently delegated to total-function defaults
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Proposition 3.7 and Definition 3.4, printed pp.11–12 / PDF 13–14; proof pp.29–30 / PDF 31–32

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem spectral_facts (s : ℕ) (hs : 2 ≤ s) (he : Even s) :
  (∀ m : ℕ, SpectralProperties (shapeA s m)) ∧
  (∀ m : ℕ, 1 ≤ m → (∀ γ ∈ Set.Icc (0 : ℝ) 1, shapeA s m γ ≤ shapeA s (m - 1) γ) ∧
    delta s (m - 1) ≤ delta s m) ∧
  (∀ m : ℕ, IsGreatest (zeroInterval s m) (delta s m)) ∧
  (∀ m : ℕ, ∀ γ ∈ Set.Icc (0 : ℝ) 1, ∃ α : ℝ, domainA α γ ∧
    shapeA s (m + 1) γ = shapeA s m α + fA α γ ∧
    ∀ a : ℝ, domainA a γ → shapeA s m a + fA a γ ≤ shapeA s (m + 1) γ) := by sorry

end CSSNearGV.Amplification
