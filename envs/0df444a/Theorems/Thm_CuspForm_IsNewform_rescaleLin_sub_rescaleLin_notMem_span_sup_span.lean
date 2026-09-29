-- Prove2me | Theorems.Thm_CuspForm_IsNewform_rescaleLin_sub_rescaleLin_notMem_span_sup_span
-- name    : CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/5b014eb1-4368-55b6-aab6-167f890dd126
-- title:
--   Difference of newforms of distinct q-levels avoids the old span
-- statement:
--   Fix natural numbers $L, L_1, q, m, e, R, R_1, R', R_1'$ with $L \neq 0$ and $q$ prime, and suppose $q^m L_1 = L$ with $q \nmid L_1$, $q^m R_1 = R$ with $q \nmid R_1$, and $q^e R_1' = R'$ with $q \nmid R_1'$, where $e < m$; thus $v_q(L) = v_q(R) = m > e = v_q(R')$. Let $g$ be a weight-$2$ cusp form on $\Gamma_0(R)$ and $g'$ a weight-$2$ cusp form on $\Gamma_0(R')$, each a newform in the sense of [`CuspForm.IsNewform`](def/CuspForm_Newforms.html#L23): a normalised eigenform (first $q$-expansion coefficient $1$, multiplicativity of $q$-coefficients at coprime indices, and the two recursions for $a_{p^{r+2}}$ according as $p$ divides the level or not) such that for no proper divisor $M$ of its level does a normalised eigenform on $\Gamma_0(M)$ have the same $q$-coefficients at all primes not dividing the level. Assume $1 \cdot R \mid L$ and $1 \cdot R' \mid L$, and write $\iota_d$ for [`FreyPackage.ModMCarrier.rescaleLin`](def/FreyPackage_ModMCarrier_Rescale.html#L140), the map $f \mapsto f \mid_2 \mathrm{diag}(d,1)$ from weight-$2$ cusp forms on $\Gamma_0(N)$ to those on $\Gamma_0(L)$ whenever $dN \mid L$. The assertion is that $\iota_1 g - \iota_1 g'$ does not lie in the join of the $\mathbb{C}$-span of $\{\iota_{q^i} g' : i \geq 1,\ q^i R' \mid L\}$ and the $\mathbb{C}$-span of $\{\iota_p x : p \text{ prime},\ p \neq q,\ pN' = L,\ x \in S_2(\Gamma_0(N'))\}$.
--
--   This is the separation step in the multiplicity-one comparison of two weight-$2$ newforms whose levels have different $q$-adic valuations: the difference of their degeneracy images at the common level $L$ is kept out of the $q$-tower of $g'$ together with the old space coming from primes other than $q$. It is used in the proof of [`CuspForm.IsNewform.level_eq_of_forall_prime_not_dvd_qCoeff_eq`](thm.html#CuspForm.IsNewform.level_eq_of_forall_prime_not_dvd_qCoeff_eq), which identifies the level of a newform from its $q$-coefficients away from the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_IsNewform_rescaleLin_sub_rescaleLin_notMem_span_sup_span.lean

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span
    {L L₁ q m e R R₁ R' R₁' : ℕ} [NeZero L] (hq : q.Prime)
    (hL : q ^ m * L₁ = L) (hqL₁ : ¬ q ∣ L₁)
    (hR : q ^ m * R₁ = R) (hqR₁ : ¬ q ∣ R₁)
    (hR' : q ^ e * R₁' = R') (hqR₁' : ¬ q ∣ R₁') (he : e < m)
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2} {g' : CuspForm (CongruenceSubgroup.Gamma0 R') 2}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (h1 : 1 * R ∣ L) (h1' : 1 * R' ∣ L) :
    FreyPackage.ModMCarrier.rescaleLin h1 2 g - FreyPackage.ModMCarrier.rescaleLin h1' 2 g' ∉
      Submodule.span ℂ {F : CuspForm (CongruenceSubgroup.Gamma0 L) 2 |
          ∃ (i : ℕ) (h : q ^ i * R' ∣ L), 1 ≤ i ∧ F = FreyPackage.ModMCarrier.rescaleLin h 2 g'}
        ⊔ Submodule.span ℂ {F : CuspForm (CongruenceSubgroup.Gamma0 L) 2 |
          ∃ (p N' : ℕ) (h : p * N' ∣ L) (x : CuspForm (CongruenceSubgroup.Gamma0 N') 2),
            p.Prime ∧ p ≠ q ∧ p * N' = L ∧ F = FreyPackage.ModMCarrier.rescaleLin h 2 x} := by sorry
