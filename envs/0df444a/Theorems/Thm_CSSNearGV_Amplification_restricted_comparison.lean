-- Prove2me | Theorems.Thm_CSSNearGV_Amplification_restricted_comparison
-- name    : CSSNearGV.Amplification.restricted_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T21:18:39.136893+00:00
-- url     : https://prove2.me/theorems/44359ed3-3957-44ed-8577-aa62084ded7d
-- title:
--   Lemma 5.4 — restricted spectral comparison
-- statement:
--   Suppose $\varphi-h$ is symmetric about $1/2$ and nonincreasing on $[0,1/2]$. For $m\ge1$, $0\le\tau\le1/2$ and $\gamma\in[0,1]$, both $Q=AD$ and $Q=DA$ satisfy
--   $$r_{Q,\ge\tau}^{(m)}(\gamma)\le\max_{\tau\le\alpha\le1-\tau}\{r_Q^{(m-1)}(\alpha)+g(\alpha,\gamma)\}
--   \le r_{A,\ge\min(\tau,\lambda_\gamma)}^{(m)}(\gamma).$$
--   Transition maxima intersect the valid transition domains. This is the paper's corrected comparison lemma.
--
--   Differences from the source:
--   - encoding: binary words, finite expectations and feasible entropy maxima → Fin-indexed binary vectors, exact finite averages and domain-restricted extrema; reason: the representation preserves the source objects and domains; endpoint values use continuous entropy extensions
--   - reading: increasing and decreasing → nondecreasing and nonincreasing; reason: the spectral shapes have zero plateaus, as used explicitly in the paper
--   - encoding: maximum over a restricted feasible domain → EReal supremum, with the empty domain assigned minus infinity; reason: the source maximum has no real value on an empty domain; every nonempty feasible maximum retains its value
-- source:
--   Rachel Yun Zhang, Linear-Time Encodable Quantum Codes near the CSS GV Bound, STOC 2027 submission #1164 (October 2026), Lemma 5.4, printed p.16 / PDF 18; proof p.17 / PDF 19

import Definitions.Def_CSSNearGV_Amplification_Estimates

open scoped BigOperators
noncomputable section

namespace CSSNearGV.Amplification

theorem restricted_comparison (s : ℕ) (hs : 2 ≤ s) (he : Even s)
  (hφsym : Symmetric (fun x => phi s x - entropy x))
  (hφmono : AntitoneOn (fun x => phi s x - entropy x) (Set.Icc 0 (1 / 2)))
  (m : ℕ) (hm : 1 ≤ m) (τ γ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) (1 / 2))
  (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
  ∀ ad : Bool, restrictedPair s m ad τ γ ≤ comparisonMax s m ad τ γ ∧
    comparisonMax s m ad τ γ ≤ restrictedA s m (min τ (lambda γ)) γ := by sorry

end CSSNearGV.Amplification
