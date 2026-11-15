-- Prove2me | Theorems.Thm_DiazModulus_ratLogAlg_mem_iff
-- name    : DiazModulus.ratLogAlg_mem_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-14T17:29:32.337628+00:00
-- url     : https://prove2.me/theorems/af6fa0a0-5c65-4662-a35d-5d458dc27895
-- title:
--   The ℚ-vector space spanned by 1 and the set ℒ of logarithms of algebraic numbers is ℚ + ℒ: x lies in it if and only if x − q ∈ ℒ for some rational q
-- statement:
--   Here $\mathcal L$ is the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic).
--
--   Let $x \in \mathbb C$. Then $x$ lies in the $\mathbb Q$-vector space spanned by $1$ and $\mathcal L$ if and only if $x - q \in \mathcal L$ for some $q \in \mathbb Q$. So this space is $\mathbb Q + \mathcal L = \{q + \lambda : q \in \mathbb Q,\ \lambda \in \mathcal L\}$.
-- source:
--   Step of the proof of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren der mathematischen Wissenschaften 326, Springer, 2000, Cor. 11.15 (p. 398), for (K, L) = (ℚ, ℚ + ℒ), by Roy's route: the space ℚ + ℒ of DALAG p. 398 as the ℚ-span of 1 and ℒ. Novelty: none claimed; routine. Formal proof: Diaz modulus mission, 14 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem ratLogAlg_mem_iff (x : ℂ) :
    x ∈ Submodule.span ℚ (insert (1 : ℂ) LogAlg) ↔ ∃ q : ℚ, x - (q : ℂ) ∈ LogAlg := by
  sorry

end DiazModulus
