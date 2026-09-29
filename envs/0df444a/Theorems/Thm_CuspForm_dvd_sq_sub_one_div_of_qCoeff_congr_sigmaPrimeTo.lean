-- Prove2me | Theorems.Thm_CuspForm_dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo
-- name    : CuspForm.dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/db7e2481-f0f4-5812-b63b-5fa186758fed
-- title:
--   Eisenstein congruence forces m ∣ (p²-1)/24
-- statement:
--   Let $p$ be a prime and let $m$ be a natural number with $2 \le m$. Assume [`CuspForm.HasIntegralBasis p`](def/CuspForm_IntegralLattice.html#L17), i.e. that the $\mathbb{C}$-span of the set of weight-two cusp forms on $\Gamma_0(p)$ all of whose $q$-expansion coefficients (the coefficients of the width-one $q$-expansion) lie in the smallest subring of $\mathbb{C}$ is the whole space. Let $f$ be a cusp form of weight $2$ on $\Gamma_0(p)$ lying in that set, so every $q$-coefficient of $f$ lies in the image of $\mathbb{Z}$ in $\mathbb{C}$, and let $af : \mathbb{N} \to \mathbb{Z}$ be integers with $af(n)$ mapping to the $n$-th $q$-coefficient of $f$ for all $n$. Assume $af(1)$ and $m$ are coprime in $\mathbb{Z}$ (in the Bézout sense), and that for every $n \neq 0$ one has $m \mid af(n) - \sigma'_p(n)\, af(1)$, where $\sigma'_p(n) = \sum_{d \mid n,\ p \nmid d} d$. Then $m$ divides $(p^2-1)/24$, the division being truncated division of natural numbers.
--
--   This is one half of Mazur's bound on the modulus of an Eisenstein congruence for weight-two forms on $\Gamma_0(p)$, the other half being divisibility of $(p-1)/2$; together they give divisibility of the numerator of $(p-1)/12$. It is used by [`CuspForm.dvd_eisensteinNumerator_of_qCoeff_congr_sigmaPrimeTo`](thm.html#CuspForm.dvd_eisensteinNumerator_of_qCoeff_congr_sigmaPrimeTo).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo.lean

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_CuspForm_IntegralLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem CuspForm.dvd_sq_sub_one_div_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (hIB : CuspForm.HasIntegralBasis p) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (hf : f ∈ CuspForm.qIntegralSet p) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (h1 : IsCoprime (af 1) (m : ℤ)) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : m ∣ (p ^ 2 - 1) / 24 := by sorry
