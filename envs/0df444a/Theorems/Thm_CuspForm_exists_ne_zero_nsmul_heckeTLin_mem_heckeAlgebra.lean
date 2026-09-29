-- Prove2me | Theorems.Thm_CuspForm_exists_ne_zero_nsmul_heckeTLin_mem_heckeAlgebra
-- name    : CuspForm.exists_ne_zero_nsmul_heckeTLin_mem_heckeAlgebra
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/79f4dd61-dfce-5826-8aa2-dcf1e9c15b30
-- title:
--   A non-zero multiple of Tₚ lies in T^S
-- statement:
--   Fix a natural number $M \neq 0$, a set $S \subseteq \mathbb{N}$ assumed finite, and a prime $p$ with $p \nmid M$. Inside the algebra $\operatorname{End}_{\mathbb{C}} S_2(\Gamma_0(M))$ of $\mathbb{C}$-linear endomorphisms of the space of weight-$2$ cusp forms for $\Gamma_0(M)$, consider [`CuspForm.heckeAlgebra M 2 S`](def/CuspForm_HeckeAlgebra.html#L18), the $\mathbb{Z}$-subalgebra generated (as `Algebra.adjoin ℤ`) by the set of those endomorphisms of one of the two shapes: [`CuspForm.heckeTLin 2 hℓ hℓM`](def/ModularForm_HeckeOperatorForms.html#L69) for a prime $\ell$ with $\ell \nmid M$ and $\ell \notin S$, or `heckeULin 2 hqM` for a prime $q$ dividing $M$ with $q \notin S$. Here [`CuspForm.heckeTLin 2 hℓ hℓM`](def/ModularForm_HeckeOperatorForms.html#L69) is the linear endomorphism of $S_2(\Gamma_0(M))$ sending $f$ to the function `heckeT 2 ℓ ⇑f`, namely `heckeU 2 ℓ ⇑f` plus the weight-$2$ slash of $f$ by `heckeDiagMatrix ℓ`, together with the verifications that this again is a weight-$2$ cusp form for $\Gamma_0(M)$. The assertion is that there exists a natural number $n \neq 0$ such that the $n$-fold sum $n \cdot$ [`CuspForm.heckeTLin 2 hp hpM`](def/ModularForm_HeckeOperatorForms.html#L69), i.e. $n\,T_p$, belongs to [`CuspForm.heckeAlgebra M 2 S`](def/CuspForm_HeckeAlgebra.html#L18); the operator $T_p$ itself is not claimed to lie in that ring.
--
--   This is the statement that the anemic weight-two Hecke ring away from a finite set $S$ of primes contains a non-zero integral multiple of $T_p$ for every prime $p \nmid M$, equivalently that $T_p$ lies in $\mathbb{T}^S(M) \otimes_{\mathbb{Z}} \mathbb{Q}$, so that $\mathbb{T}^S(M)$ has finite index in $\mathbb{T}^S(M)[T_p]$. It is used in the local study of the Hecke algebra, in [`CuspForm.heckeLocal.exists_isNewform_chig_iota_of_point_of_not_dvd`](thm.html#CuspForm.heckeLocal.exists_isNewform_chig_iota_of_point_of_not_dvd), to pass from points of the spectrum of the anemic Hecke ring to newforms with prescribed eigenvalues at all primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_ne_zero_nsmul_heckeTLin_mem_heckeAlgebra.lean

import Definitions.Def_CuspForm_HeckeAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_ne_zero_nsmul_heckeTLin_mem_heckeAlgebra
    (M : ℕ) [NeZero M] (S : Set ℕ) (hS : S.Finite) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    ∃ n : ℕ, n ≠ 0 ∧
      n • (CuspForm.heckeTLin 2 hp hpM : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) ∈
        CuspForm.heckeAlgebra M 2 S := by sorry
