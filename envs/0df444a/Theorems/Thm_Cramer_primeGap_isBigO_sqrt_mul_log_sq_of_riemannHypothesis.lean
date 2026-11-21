-- Prove2me | Theorems.Thm_Cramer_primeGap_isBigO_sqrt_mul_log_sq_of_riemannHypothesis
-- name    : Cramer.primeGap_isBigO_sqrt_mul_log_sq_of_riemannHypothesis
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:41:42.240561+00:00
-- url     : https://prove2.me/theorems/9a653538-4c38-4907-a35c-39fd255ae484
-- title:
--   Under RH, prime gaps are $O(\sqrt{p_n}\log^2 p_n)$
-- statement:
--   Assume the Riemann hypothesis, in Mathlib's form `RiemannHypothesis`. Let $p_n$ be the $n$-th prime ($p_0=2$) and $g_n=p_{n+1}-p_n$ the $n$-th prime gap. Then
--
--   $$g_n=O\!\left(\sqrt{p_n}\,\log^2 p_n\right)\qquad(n\to\infty).$$
--
--   This is the classical consequence of RH for gaps between consecutive primes. Cramér (1920) proved the sharper bound $O(\sqrt{p_n}\log p_n)$ by a smoothed explicit formula; the stated bound is the weaker form. It follows directly from the von Koch-type estimate $\theta(x)=x+O(\sqrt x\log^2x)$: an interval $(x,x+C\sqrt x\log^2x]$ always contains a prime for large $x$.
--
--   **Formalization Note.** $g_n$ is `LindelofHypothesis.primeGap n` $=$ `Nat.nth Nat.Prime (n+1) - Nat.nth Nat.Prime n`, from the definitions bundle `LindelofHypothesis_GrowthAndZeroCounts`, also used by `LindelofHypothesis.ingham_primeGap_of_lindelof`. The $O$ is `Asymptotics.IsBigO` along `Filter.atTop` on $\mathbb N$.
-- source:
--   H. Cramér, Some theorems concerning prime numbers, Ark. Mat. Astr. Fys. 15 (1920), no. 5 (under RH, p_{n+1} - p_n = O(√p_n log p_n)); the stated O(√p_n log² p_n) is the weaker bound obtained from θ(x) = x + O(√x log² x) under RH (von Koch 1901). See also H. L. Montgomery and R. C. Vaughan, Multiplicative Number Theory I, Cambridge Univ. Press 2007, §13.1 (Exercise on primes in short intervals under RH).

import Mathlib
import Definitions.Def_LindelofHypothesis_GrowthAndZeroCounts

namespace Cramer

theorem primeGap_isBigO_sqrt_mul_log_sq_of_riemannHypothesis (hRH : RiemannHypothesis) :
    (fun n : ℕ => (LindelofHypothesis.primeGap n : ℝ)) =O[Filter.atTop]
      (fun n : ℕ => Real.sqrt (Nat.nth Nat.Prime n : ℝ) * Real.log (Nat.nth Nat.Prime n : ℝ) ^ 2) := by sorry

end Cramer
