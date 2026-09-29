-- Prove2me | Theorems.Thm_CuspForm_dvd_eisensteinNumerator_of_qCoeff_congr_sigmaPrimeTo
-- name    : CuspForm.dvd_eisensteinNumerator_of_qCoeff_congr_sigmaPrimeTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/9945e3c3-a550-5de7-9dc0-a0a81b550b34
-- title:
--   Eisenstein congruence mod m forces m ∣ n(p)
-- statement:
--   Let $p$ be a prime and $m$ a natural number with $2 \le m$. Assume [`CuspForm.HasIntegralBasis p`](def/CuspForm_IntegralLattice.html#L17), i.e. that the $\mathbb{C}$-span of the set of those weight-two cusp forms on $\Gamma_0(p)$ all of whose $q$-expansion coefficients lie in the smallest subring of $\mathbb{C}$ is the whole space. Let $f$ be a weight-two cusp form on $\Gamma_0(p)$ lying in that set, so every coefficient [`ModularFormClass.qCoeff f n`](def/FLTPrelim_Modularity.html#L19) (the $n$-th coefficient of the $q$-expansion of $f$ with respect to the parameter of width $1$) belongs to the bottom subring of $\mathbb{C}$. Let $af : \mathbb{N} \to \mathbb{Z}$ be integers with $(af\,n : \mathbb{C}) =$ `qCoeff f n` for all $n$, suppose $af\,1$ and $m$ are coprime in $\mathbb{Z}$, and suppose that for every $n \neq 0$ one has $m \mid af\,n - \sigma'_p(n)\, af\,1$, where $\sigma'_p(n)$ is the sum of those divisors of $n$ not divisible by $p$. Then $m$ divides `eisensteinNumerator p`, defined as the natural-number quotient $(p-1)/\gcd(p-1,12)$.
--
--   This is the constant-term (Eisenstein congruence) step in Mazur's computation of the index of the Eisenstein ideal: a weight-two form on $\Gamma_0(p)$ congruent mod $m$, away from the constant term, to a multiple of the weight-two Eisenstein series can exist only if $m$ divides the numerator $n(p)$ of $(p-1)/12$, the order of the cuspidal group of $J_0(p)$. It is used in the construction of an element of the Eisenstein ideal whose Hecke projection realises `eisensteinNumerator p`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_dvd_eisensteinNumerator_of_qCoeff_congr_sigmaPrimeTo.lean

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_CuspForm_IntegralLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem CuspForm.dvd_eisensteinNumerator_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (hIB : CuspForm.HasIntegralBasis p) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (hf : f ∈ CuspForm.qIntegralSet p) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (h1 : IsCoprime (af 1) (m : ℤ)) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : m ∣ eisensteinNumerator p := by sorry
