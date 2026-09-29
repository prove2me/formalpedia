-- Prove2me | Theorems.Thm_CuspForm_exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq
-- name    : CuspForm.exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/c03d3f4f-fc2a-5164-9c5d-607776ab74da
-- title:
--   Conjugation by diag(q,1) transports weight-two cusp forms and periods
-- statement:
--   Let $q$ be a prime and $M'\ge 1$ a natural number with $q\nmid M'$, and let $H\le(\mathbb{Z}/q^2M')^\times$ be the kernel of the reduction map $(\mathbb{Z}/q^2M')^\times\to(\mathbb{Z}/q)^\times$ coming from $q\mid q^2M'$; here [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) $(q^2M')\,H$ denotes the subgroup of $\mathrm{SL}_2(\mathbb{Z})$ consisting of the elements of $\Gamma_0(q^2M')$ whose lower-right entry, read as a unit modulo $q^2M'$, lies in $H$, i.e. is $\equiv 1 \bmod q$. Three assertions are made. First, for every $\gamma\in\Gamma(q)\cap\Gamma_0(M')$ there is a $\gamma'$ in that group $\Gamma_H$ with $\gamma_{00}=\gamma'_{00}$, $\gamma_{01}=q\,\gamma'_{01}$, $q\,\gamma_{10}=\gamma'_{10}$ and $\gamma_{11}=\gamma'_{11}$ (the entrywise form of $\gamma=\operatorname{diag}(q,1)\gamma'\operatorname{diag}(q,1)^{-1}$); secondly, the same correspondence is surjective the other way, every such $\gamma'$ arising from some $\gamma$. Thirdly, there exists a $\mathbb{C}$-linear isomorphism $L$ from weight-two cusp forms for $\Gamma(q)\cap\Gamma_0(M')$ to weight-two cusp forms for $\Gamma_H(q^2M')$ such that the function underlying $L F$ is the weight-two slash $F\mid_2 \operatorname{diag}(q,1)$ (the matrix [`ModularForm.heckeDiagMatrix`](def/ModularForm_HeckeOperator.html#L21) $q$, namely $\begin{pmatrix}q&0\\0&1\end{pmatrix}\in \mathrm{GL}_2(\mathbb{R})$ as $q\neq 0$), and such that for any $\gamma,\gamma'$ related by the four entry identities above and any $F$, the period functional [`ModularCurve.periodOf`](def/ModularCurve_PeriodOf.html#L56) of $\gamma'$ evaluated at $L F$ equals that of $\gamma$ evaluated at $F$, where [`ModularCurve.periodOf`](def/ModularCurve_PeriodOf.html#L56) $\Gamma\,\gamma$ is integration of a weight-two cusp form along the path from $i$ to $\gamma\cdot i$.
--
--   This is the standard identification of $\Gamma_H(q^2M')$ with $\Gamma(q)\cap\Gamma_0(M')$ by conjugation by $\operatorname{diag}(q,1)$, together with the induced isomorphism $F\mapsto F\mid_2\operatorname{diag}(q,1)$ on weight-two cusp forms and the resulting matching of periods, hence of period lattices. It is used in the passage from forms of level $\Gamma(q)\cap\Gamma_0(M')$ to forms of $\Gamma_H$-type level, by [`CuspForm.IsNewform.exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType`](thm.html#CuspForm.IsNewform.exists_linearMap_fixedSubmodule_H1_gammaH_laws_of_isCuspidalOfType) and by [`ModularCurve.FullLevel.exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span`](thm.html#ModularCurve.FullLevel.exists_injective_dual_baseChange_tateModule_jac_of_isNewform_of_range_eq_span).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq.lean

import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_CohCarrier_Level
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups ModularForm

theorem CuspForm.exists_linearEquiv_gamma_inf_gamma0_gammaH_slash_heckeDiagMatrix_and_periodOf_eq
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') :
    (∀ γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)),
        ∃ γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker),
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
          (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ∧
    (∀ γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker),
        ∃ γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)),
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ∧
          (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 ∧
          ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1) ∧
    ∃ L : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2 ≃ₗ[ℂ]
        CuspForm (CohCarrier.GammaH (q ^ 2 * M')
          (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker) 2,
      (∀ F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2,
          ⇑(L F) = (⇑F) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) ∧
      ∀ (γ : ↥(CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)))
        (γ' : ↥(CohCarrier.GammaH (q ^ 2 * M')
            (ZMod.unitsMap (dvd_mul_of_dvd_left (dvd_pow_self q two_ne_zero) M')).ker)),
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 →
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q * ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 →
        (q : ℤ) * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 →
        ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 →
          ∀ F : CuspForm (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) 2,
            ModularCurve.periodOf _ γ' (L F) = ModularCurve.periodOf (CongruenceSubgroup.Gamma q ⊓ CongruenceSubgroup.Gamma0 M' : Subgroup SL(2, ℤ)) γ F := by sorry
