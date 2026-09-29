-- Prove2me | Theorems.Thm_CerednikDrinfeld_uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet
-- name    : CerednikDrinfeld.uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/550eba32-e72e-56e3-8538-3e0a1c75712b
-- title:
--   Two descriptions of the Uₛ-set on the meet order agree
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q'$ be a prime such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsDefiniteRamifiedExactlyAt`, i.e. $a<0$, $b<0$, and for every height-one prime $v$ of $\mathbb{Z}$ the completion $\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division ring (every nonzero element is a unit) exactly when $q'\in v$. Let $M$ be a nonzero natural number and let $\Lambda, R$ be $\mathbb{Z}$-submodules of $\mathbb{H}$ with: $\Lambda$ a maximal order (an order maximal among orders containing it); $R$ an Eichler order of level $M$, that is $R=\Lambda_1\cap\Lambda_2$ for maximal orders $\Lambda_1,\Lambda_2$ with the relative index of $R$ in $\Lambda_1$ equal to $M$; and $R\le\Lambda$. Let $s$ be a prime with $s\neq q'$ and $s\nmid M$, and let $n$ be a unit of $\mathbb{H}\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ lying in the degree-$s$ Hecke set of $R$: $n$ lies in the adelic box $\hat R$, $s\,n^{-1}$ lies in $\hat R$, while $n^{-1}\notin\hat R$ and $s^{-1}n\notin\hat R$. Write $S=R\cap nRn^{-1}$ for the meet order, where $nRn^{-1}$ denotes $\mathbb{H}\cap n\hat R n^{-1}$. Then the two sets of units coincide: the set of $h$ in the degree-$s$ Hecke set of $S$ with $h(n\hat Rn^{-1})h^{-1}\cap\mathbb{H}=R$ and $h\hat Rh^{-1}\cap\mathbb{H}\neq nRn^{-1}$ equals the set of $h$ in the degree-$s$ Hecke set of $S$ with $h\hat Sh^{-1}\cap\mathbb{H}\neq S$ and $S\not\le h\hat\Lambda h^{-1}\cap\mathbb{H}$.
--
--   This identifies, at an auxiliary prime $s$ away from the ramification $q'$ and from the Eichler level $M$, the adelic set defining the operator $U_s$ on the class set of the meet order $R\cap nRn^{-1}$ with the description given in terms of a maximal order $\Lambda$ above $R$; locally at $s$ the two conditions express the same statement about oriented edges of the Bruhat–Tits tree of $\mathrm{GL}_2(\mathbb{Q}_s)$. It is used in the construction of the equivalence of class sets compatible with the degeneracy maps and the Hecke action, [`CerednikDrinfeld.exists_equiv_classSet_ssPlaces_degeneracy_hecke_comm`](thm.html#CerednikDrinfeld.exists_equiv_classSet_ssPlaces_degeneracy_hecke_comm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet.lean

import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {M : ℕ} [NeZero M] (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R M) (hRΛ : R ≤ Λ)
    {s : ℕ} [Fact s.Prime] (hsq' : s ≠ q') (hsM : ¬ s ∣ M)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R s) :
    uHeckeSet R n s = levelHeckeUSet Λ (meetOrder R n) s := by sorry
