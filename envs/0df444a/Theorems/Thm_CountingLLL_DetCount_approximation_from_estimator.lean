-- Prove2me | Theorems.Thm_CountingLLL_DetCount_approximation_from_estimator
-- name    : CountingLLL.DetCount.approximation_from_estimator
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:50:25.124215+00:00
-- url     : https://prove2.me/theorems/28b36f91-600f-4efb-8f32-1f7e5d7f6402
-- title:
--   Counting accuracy from truncated marginals
-- statement:
--   Let $\Phi$ be a finite CSP satisfying Condition 1.1, with $m$ constraints, and fix a valid enumeration choice for the truncated marginal estimator. For $0\le\varepsilon\le1$, if $L$ satisfies
--
--   $$8m(0.9)^L\le\varepsilon/4,$$
--
--   then the product of the estimated conditional satisfaction probabilities, multiplied by the total number of assignments, is within relative error $\varepsilon$ of $Z_\Phi$. This is the mathematical accuracy step in the proof of Theorem 1.2; it does not assert a machine implementation or running-time bound.
-- source:
--   Liu, Wang, Yin, Zhang, and Zhou, A Counting and Sampling Lovász Local Lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf, Section 4.2, equation (21) and proof of Theorem 1.2.

import Definitions.Def_CountingLLL_DetCount_Expansion
open scoped Classical BigOperators

namespace CountingLLL.DetCount
open CSP

/-- Section 4.2: truncation accuracy implies multiplicative counting accuracy. -/
theorem approximation_from_estimator (Φ : CSP) (hΦ : Φ.Condition11)
    (L : ℕ) (en : Φ.EnumChoice) (hen : Φ.ValidEnum en) (ε : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hL : (Φ.m : ℝ) * (8*(0.9 : ℝ)^L) ≤ ε/4) :
    let Cpre : ℕ → Finset (Fin Φ.m) :=
      fun i => Finset.univ.filter (fun j : Fin Φ.m => j.val < i)
    let Zhat : ℝ := (∏ v, (Φ.q v : ℝ)) *
      ∏ i : Fin Φ.m, (1 - Φ.rhatWith en L (Cpre (i.val+1)) i)
    (1-ε)*(Φ.ZPhi : ℝ) ≤ Zhat ∧ Zhat ≤ (1+ε)*(Φ.ZPhi : ℝ) := by sorry
end CountingLLL.DetCount
