-- Prove2me | Theorems.Thm_CountingLLL_DetCount_dyadic_truncation_accuracy
-- name    : CountingLLL.DetCount.dyadic_truncation_accuracy
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:19:15.02407+00:00
-- url     : https://prove2.me/theorems/89cc0fe1-2fff-4780-abb2-a272f0c73271
-- title:
--   Explicit logarithmic truncation gives dyadic counting accuracy
-- statement:
--   Let $\Phi$ satisfy Condition 1.1 and have $m$ constraints. Fix a valid enumeration choice and a nonnegative integer $s$, and set $\varepsilon=2^{-s}$ and
--
--   $$L=10\bigl(s+\lfloor\log_2(m+1)\rfloor+6\bigr).$$
--
--   The product of the corresponding budget-$L$ estimated conditional satisfaction probabilities, multiplied by the number of all assignments, lies between $(1-\varepsilon)Z_\Phi$ and $(1+\varepsilon)Z_\Phi$. This makes the logarithmic truncation used in Section 4.2 explicit; it asserts accuracy, while the program construction and cost bound remain separate.
-- source:
--   Liu, Wang, Yin, Zhang, and Zhou, A Counting and Sampling Lovász Local Lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf, §4.2, equation (21) and proof of Theorem 1.2; an explicit sufficient truncation choice.

import Definitions.Def_CountingLLL_DetCount_Expansion
open scoped Classical BigOperators

namespace CountingLLL.DetCount
open CSP
/-- A concrete logarithmic truncation budget yields dyadic relative accuracy. -/
theorem dyadic_truncation_accuracy (Φ : CSP) (hΦ : Φ.Condition11)
    (en : Φ.EnumChoice) (hen : Φ.ValidEnum en) (s : ℕ) :
    let ε : ℝ := (1/2)^s
    let L := 10 * (s + Nat.log2 (Φ.m+1) + 6)
    let Cpre : ℕ → Finset (Fin Φ.m) :=
      fun i => Finset.univ.filter (fun j : Fin Φ.m => j.val < i)
    let Zhat : ℝ := (∏ v, (Φ.q v : ℝ)) *
      ∏ i : Fin Φ.m, (1 - Φ.rhatWith en L (Cpre (i.val+1)) i)
    (1-ε)*(Φ.ZPhi : ℝ) ≤ Zhat ∧ Zhat ≤ (1+ε)*(Φ.ZPhi : ℝ) := by sorry
end CountingLLL.DetCount
