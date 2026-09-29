-- Prove2me | Theorems.Thm_EulerMascheroni_Arithmetic_integral_of_prime_local_multiples
-- name    : EulerMascheroni.Arithmetic.integral_of_prime_local_multiples
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T16:02:45.457343+00:00
-- url     : https://prove2.me/theorems/e6d7dc93-3484-4865-9198-280322903843
-- title:
--   Prime-local integer multiples imply global algebraic integrality
-- statement:
--   Let $x\in\mathbb R$. Suppose for every prime $p$ there is an integer $d$, not divisible by $p$, such that $dx$ is integral over $\mathbb Z$. Then $x$ is integral over $\mathbb Z$. No algebraicity assumption on $x$ is required. The integers that multiply $x$ into an algebraic integer form an ideal of $\mathbb Z$; the hypotheses prevent its generator from having any prime divisor.
-- source:
--   Integral closedness and principal ideals over the integers; prime-local reformulation of the Euler factorial quotient arithmetic division conjecture. Compare Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Conjecture 2, and Matala-aho–Zudilin, https://arxiv.org/html/1703.02633, Section 2.

import Mathlib

theorem EulerMascheroni.Arithmetic.integral_of_prime_local_multiples (x : ℝ)
    (h : ∀ p : ℕ, p.Prime → ∃ d : ℤ, ¬(p:ℤ) ∣ d ∧ IsIntegral ℤ ((d:ℝ)*x)) :
    IsIntegral ℤ x := by sorry
