-- Prove2me | Theorems.Thm_Deep_NTSupply_count_coe_finprod_primeUnit_zpow
-- name    : Deep.NTSupply.count_coe_finprod_primeUnit_zpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/e2219927-7860-526f-b83e-3b06dd4f8be0
-- title:
--   Exponent of w in a finitely supported product of prime fractional ideals
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, let $n$ be an integer-valued function on the height-one spectrum of $\mathcal O_K$ (the set of nonzero prime ideals, i.e. the finite places) whose support is finite, and let $w$ be one such prime. For each prime $v$, `primeUnit K v` denotes the unit of the monoid of fractional ideals of $\mathcal O_K$ in $K$ obtained from the nonzero integral ideal $v$ via `FractionalIdeal.mk0`, that is the invertible fractional ideal $\mathfrak p_v$. Form the multiplicative finitary product $\prod^{f}_{v} \mathrm{primeUnit}\,K\,v^{\,n_v}$ in the unit group $(\mathrm{FractionalIdeal}\,(\mathcal O_K)^{0}\,K)^{\times}$, and regard it as a fractional ideal via the coercion. The assertion is that `FractionalIdeal.count K w` of this fractional ideal, the exponent with which $w$ occurs in its factorisation, equals $n_w$.
--
--   This is unique factorisation of fractional ideals of a Dedekind domain in the form needed to read off the exponent vector of a product of prime powers, the finite support hypothesis making the finitary product meaningful. It serves as a bookkeeping step in the passage between idèles, their ideal contents and ray classes, and is used in the computation of the count of the content homomorphism on Hecke characters ([`HeckeCharacter.count_coe_fadContentHom`](thm.html#HeckeCharacter.count_coe_fadContentHom)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deep_NTSupply_count_coe_finprod_primeUnit_zpow.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply HeckeCharacter LanglandsTunnell.P2.Artin
open scoped nonZeroDivisors IsMulCommutative

theorem Deep.NTSupply.count_coe_finprod_primeUnit_zpow
    (K : Type*) [Field K] [NumberField K]
    (n : HeightOneSpectrum (𝓞 K) → ℤ) (hn : (Function.support n).Finite) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w
      (((∏ᶠ v : HeightOneSpectrum (𝓞 K), primeUnit K v ^ n v : (FractionalIdeal ((𝓞 K)⁰) K)ˣ)) :
        FractionalIdeal ((𝓞 K)⁰) K) = n w := by sorry
