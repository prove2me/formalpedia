-- Prove2me | Theorems.Thm_BanditCovariates_SE_phi_variation
-- name    : BanditCovariates.SE.phi_variation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:51.471017+00:00
-- url     : https://prove2.me/theorems/b0782416-c19d-4006-9411-b5f037b10315
-- title:
--   §2, p. 9 — comparison of the φ function
-- statement:
--   For $a>0$, define $\phi_a(x)=\overline{\log}(a x^2)/x$ for $x>0$. If $x\ge x'>0$, then
--
--   $$\phi_a(x)\le2e^{-1/2}\phi_a(x').$$
--
--   The comparison replaces a sum over distinct arm gaps by a bound at one cutoff in the final step of Theorem 2.1.
--
--   **Formalization Note** Here $a=T/(18\gamma^2)$ in the paper's application. The page prints $n$ in that slot and swaps $x,x'$ in the sentence applying the inequality; the derivation from (2.2) and the theorem require $T$ and the order stated here.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 9, φ-variation display and paragraph after (2.7)

import Mathlib
import Definitions.Def_BanditCovariates_SE_Setting

namespace BanditCovariates.SE

/-- The comparison of φ on p. 9, using T in the overlined logarithm. -/
theorem phi_variation (a x x' : ℝ) (ha : 0 < a) (hx' : 0 < x')
    (hxx' : x' ≤ x) :
    phi a x ≤ 2 * Real.exp (-(1 / 2 : ℝ)) * phi a x' := by sorry

end BanditCovariates.SE
