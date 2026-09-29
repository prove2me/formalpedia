-- Prove2me | Theorems.Thm_CuspForm_AuxLevel_isEis_of_iDeg_one_add_iDeg_eq_zero
-- name    : CuspForm.AuxLevel.isEis_of_iDeg_one_add_iDeg_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/dff1f932-db63-54c6-b49e-3bbc0aaa0bf3
-- title:
--   Ihara's lemma at an auxiliary prime: kernel pairs are Eisenstein
-- statement:
--   Fix a commutative ring $R$ and an $R$-module $A$, a nonzero natural number $\ell_0$, and natural numbers $N$, $r$ with $r \neq 0$, $r$ prime and $r \nmid N$. Here $H^1(M,H,A)$ denotes [`CohCarrier.H1`](def/CohCarrier_Level.html#L162), the additive homomorphisms from $\Gamma_H(M)$ (the preimage in $\Gamma_0(M)$ of $H \le (\mathbb{Z}/M)^\times$), written additively, into $A$. Let [`CuspForm.AuxLevel.subgroup N r`](def/CuspForm_AuxLevelHeckeModule.html#L19) be the kernel of $(\mathbb{Z}/Nr)^\times \to (\mathbb{Z}/r)^\times$, so that the associated group is $\Gamma_0(Nr) \cap \Gamma_1(r)$ in the relevant sense. Assume given [`CohCarrier.LevelLE`](def/CohCarrier_Level.html#L330) data for the pairs $(N, Nr)$, $(\top, \mathrm{subgroup}\ N\ r)$ with $d = 1$ and with $d = r$, i.e. $N \mid Nr$, $d \mid r$, and compatibility of the unit subgroups; these provide the two degeneracy maps `iDeg'`, given by precomposition with $\gamma \mapsto$ `conjLowerMat d` $\gamma$. Assume further that $(r-1) \cdot a = 0$ forces $a = 0$ in $A$, that $\ell_0$ is prime with $\ell_0 \nmid Nr$, and that $g, h \in H^1(N, \top, A)$ satisfy $i_1^* g + i_r^* h = 0$. Then both $g$ and $h$ are Eisenstein for $\ell_0$: the transfer Hecke operator `heckeT` at $\ell_0$ sends each of them to $((\ell_0 : R) + 1)$ times itself.
--
--   This is the form of Ihara's lemma used at the auxiliary prime in the Taylor–Wiles argument: a pair in the kernel of the level-raising map from level $N$ to the auxiliary level $\Gamma_0(Nr)\cap\Gamma_1(r)$ is Eisenstein at every prime $\ell_0$ away from $Nr$. It is used in the construction of the linear equivalence [`CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML`](thm.html#CuspForm.AuxLevel.exists_linearEquiv_baseML_prod_ML) between the base Hecke module and a product at the auxiliary level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_AuxLevel_isEis_of_iDeg_one_add_iDeg_eq_zero.lean

import Definitions.Def_CohCarrier_Tower
import Definitions.Def_CuspForm_AuxLevelHeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.AuxLevel.isEis_of_iDeg_one_add_iDeg_eq_zero
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N r : ℕ) [NeZero r] (hr : r.Prime) (hrN : ¬ r ∣ N)
    (h₁ : CohCarrier.LevelLE N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1)
    (hr' : CohCarrier.LevelLE N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) r)
    (hA : ∀ a : A, (r - 1) • a = 0 → a = 0)
    (hℓ : ℓ₀.Prime) (hℓNr : ¬ ℓ₀ ∣ N * r)
    (g h : CohCarrier.H1 N ⊤ A)
    (hgh : CohCarrier.iDeg' N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) 1 A h₁ g +
      CohCarrier.iDeg' N (N * r) ⊤ (CuspForm.AuxLevel.subgroup N r) r A hr' h = 0) :
    CohCarrier.IsEis R A N ⊤ ℓ₀ g ∧ CohCarrier.IsEis R A N ⊤ ℓ₀ h := by sorry
