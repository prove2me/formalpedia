-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_two_mul_eq_four_mul_sub_of_map_eq_pow_smul_inv_of_hasKernelOfDegree
-- name    : CerednikDrinfeld.FormalODModule.two_mul_eq_four_mul_sub_of_map_eq_pow_smul_inv_of_hasKernelOfDegree
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/0435ab8c-add2-559f-a064-bcb4dcb69c76
-- title:
--   Kernel degree pins the central exponent: 2m' = 4(k-c)
-- statement:
--   Let $r$ be a prime and let $B_0$ be a nontrivial commutative Noetherian ring. Let $\Phi$ be a `FormalODModule` over $B_0$ for $r$, that is: a commutative two-dimensional formal group law $\Phi.F$ over $B_0$ together with series $\Phi.\mathrm{act}(a)$ ($a$ in the ring `Zp2 r`) and $\Phi.\mathrm{varpi}$, all endomorphisms of $\Phi.F$, with $\mathrm{act}$ multiplicative and additive, $\mathrm{act}(1)$ the identity, $\mathrm{varpi}\circ\mathrm{varpi}=\mathrm{act}(r)$ and $\mathrm{varpi}\circ\mathrm{act}(a)=\mathrm{act}(\mathrm{Frob}\,a)\circ\mathrm{varpi}$. Assume $\Phi$ has height $4$: the series $\Phi.\mathrm{act}(r)$ has kernel algebra finite and projective over $B_0$, of rank $r^4$ after base change along every ring homomorphism from $B_0$ to a field. Let $K_0$ be a field of characteristic zero and let $E_0$ be an injective ring homomorphism from the centraliser in $\mathrm{End}(\Phi.F)$ of the set $\{\Phi.\mathrm{actEnd}(a)\}_a\cup\{\Phi.\mathrm{varpiEnd}\}$ into $M_2(K_0)$. Let $e$ lie in that centraliser, let $k,m'$ be natural numbers and $c$ an integer, and suppose $E_0(e)=r^{k}\cdot\big((r\cdot 1)^{c}\big)^{-1}$, the inverse being taken in $\mathrm{GL}_2(K_0)$ of the $c$-th power of the scalar matrix $r$. Suppose further that the series of $e$ has kernel of degree $r^{2m'}$ in the above sense. Then $2m' = 4(k-c)$ as integers.
--
--   The statement is the numerical compatibility underlying the Čerednik–Drinfeld comparison: for an endomorphism of a height-$4$ formal $\mathcal{O}_D$-module whose image under a faithful two-dimensional representation is the central scalar $r^{k-c}$, the degree of its kernel forces the exponent relation $2m'=4(k-c)$. It is used in the rigidification bookkeeping for fake elliptic curves, in the lemmas identifying the level index $n$ under rigid transport along a Frobenius twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_two_mul_eq_four_mul_sub_of_map_eq_pow_smul_inv_of_hasKernelOfDegree.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.two_mul_eq_four_mul_sub_of_map_eq_pow_smul_inv_of_hasKernelOfDegree
    {r : ℕ} [Fact r.Prime] {B₀ : Type} [CommRing B₀] [IsNoetherianRing B₀] [Nontrivial B₀]
    (Φ : FormalODModule r B₀) (hΦ4 : Φ.HasHeight 4)
    {K₀ : Type} [Field K₀] [CharZero K₀]
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
    (hE₀ : Function.Injective E₀)
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (k m' : ℕ) (c : ℤ)
    (hE : E₀ e = (r : K₀) ^ k •
      ((((Units.map (algebraMap K₀ (Matrix (Fin 2) (Fin 2) K₀)).toMonoidHom
              (Units.mk0 (r : K₀) (Nat.cast_ne_zero.mpr (Fact.out : r.Prime).ne_zero))) ^ c)⁻¹ :
          Matrix.GeneralLinearGroup (Fin 2) K₀) : Matrix (Fin 2) (Fin 2) K₀))
    (hdeg : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m'))) :
    (2 * m' : ℤ) = 4 * ((k : ℤ) - c) := by sorry
