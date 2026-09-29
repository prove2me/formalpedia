-- Prove2me | Theorems.Thm_Algebra_Smooth_isIntegrallyClosed_quotient_of_mem_minimalPrimes
-- name    : Algebra.Smooth.isIntegrallyClosed_quotient_of_mem_minimalPrimes
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/7ccc558e-90d7-5d8c-b440-f2c486b13a84
-- title:
--   Quotients of a smooth algebra by minimal primes are normal
-- statement:
--   Let $K$ be a field and let $S$ be a commutative $K$-algebra (both in the same universe) which is smooth over $K$ in the sense of Mathlib's `Algebra.Smooth`, i.e. formally smooth and of finite presentation over $K$. Let $\mathfrak p$ be an ideal of $S$ lying in `minimalPrimes S`, that is, $\mathfrak p$ is minimal among the prime ideals of $S$ containing the zero ideal (so in particular $\mathfrak p$ is prime and $S/\mathfrak p$ is a domain). The conclusion is that the quotient ring $S \mathbin{⧸} \mathfrak p$ is integrally closed: every element of its fraction field which is integral over $S/\mathfrak p$ already lies in the image of $S/\mathfrak p$. Thus the coordinate ring of an irreducible component of $\operatorname{Spec} S$, for $S$ smooth over a field, is a normal domain. No hypothesis is imposed on $K$ beyond being a field, and no separability or reducedness hypothesis on $S$ is needed.
--
--   This is the algebraic form of the statement that the irreducible components of a smooth scheme over a field are normal. It is used to verify normality of the rings arising from components of moduli problems attached to modular curves, being cited in the treatment of quotients of tensor products by minimal primes at full level for $\Gamma_0$- and $H_1$-type rigid data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_Smooth_isIntegrallyClosed_quotient_of_mem_minimalPrimes.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem Algebra.Smooth.isIntegrallyClosed_quotient_of_mem_minimalPrimes
    (K : Type u) [Field K] (S : Type u) [CommRing S] [Algebra K S] [Algebra.Smooth K S]
    (𝔭 : Ideal S) (h𝔭 : 𝔭 ∈ minimalPrimes S) :
    IsIntegrallyClosed (S ⧸ 𝔭) := by sorry
