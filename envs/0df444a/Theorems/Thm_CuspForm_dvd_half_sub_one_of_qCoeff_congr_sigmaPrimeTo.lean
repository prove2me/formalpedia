-- Prove2me | Theorems.Thm_CuspForm_dvd_half_sub_one_of_qCoeff_congr_sigmaPrimeTo
-- name    : CuspForm.dvd_half_sub_one_of_qCoeff_congr_sigmaPrimeTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/4775572a-0d9b-5564-ac43-cf5b0c49e448
-- title:
--   Eisenstein congruences on Γ₀(p) force m ∣ (p-1)/2
-- statement:
--   Let $p$ be a prime and let $m$ be a natural number with $2 \le m$. Assume [`CuspForm.HasIntegralBasis p`](def/CuspForm_IntegralLattice.html#L17), i.e. that the $\mathbb{C}$-span of the set of weight-two cusp forms on $\Gamma_0(p)$ all of whose $q$-expansion coefficients (the coefficients of the $q$-expansion of width $1$) lie in the smallest subring of $\mathbb{C}$ is the whole space. Let $f$ be a cusp form of weight $2$ on $\Gamma_0(p)$ belonging to that set, so every coefficient of its $q$-expansion lies in the smallest subring of $\mathbb{C}$. Let $af : \mathbb{N} \to \mathbb{Z}$ be integers whose images in $\mathbb{C}$ are the $q$-expansion coefficients of $f$, so that $af\,n$ is the $n$-th coefficient. Assume $af\,1$ and $m$ are coprime in $\mathbb{Z}$, and that for every $n \neq 0$ one has $m \mid af\,n - \sigma'_p(n)\, af\,1$, where $\sigma'_p(n)$ is the sum of those divisors of $n$ not divisible by $p$. The conclusion is that $m$ divides the natural-number quotient $(p-1)/2$.
--
--   This is one of the two halves of the Eisenstein-quotient divisibility of Mazur's study of the Eisenstein ideal: a weight-two cusp form on $\Gamma_0(p)$ whose Hecke eigenvalues are congruent mod $m$ to those of the Eisenstein series $\sigma'_p$ forces $m \mid (p-1)/2$. It is used to derive the divisibility of $m$ by the numerator of $(p-1)/12$ in [`CuspForm.dvd_eisensteinNumerator_of_qCoeff_congr_sigmaPrimeTo`](thm.html#CuspForm.dvd_eisensteinNumerator_of_qCoeff_congr_sigmaPrimeTo).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_dvd_half_sub_one_of_qCoeff_congr_sigmaPrimeTo.lean

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_CuspForm_IntegralLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem CuspForm.dvd_half_sub_one_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (hIB : CuspForm.HasIntegralBasis p) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (hf : f ∈ CuspForm.qIntegralSet p) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (h1 : IsCoprime (af 1) (m : ℤ)) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : m ∣ (p - 1) / 2 := by sorry
