-- Prove2me | Theorems.Thm_CerednikDrinfeld_ribbon_kernelEquiv
-- name    : CerednikDrinfeld.ribbon_kernelEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/8e039ffa-113b-547d-a988-17269f1f5d34
-- title:
--   Matched Hecke data: isometric equivariant ribbon kernels
-- statement:
--   Let $E_1,V_1,E_2,V_2$ be finite types (with decidable equality on $V_1,V_2$), and for $i=1,2$ let $D_i$ be degeneracy data on $(E_i,V_i)$, that is maps $a_i,b_i\colon E_i\to V_i$ together with positive integer widths $w_i\colon E_i\to\mathbb{N}^+$. Write $\delta_i^0,\delta_i^1\colon (E_i\to\mathbb{Z})\to(V_i\to\mathbb{Z})$ for the pushforwards along $a_i$ and $b_i$, let the ribbon kernel $\mathrm{ribbonKernel}\,D_i$ be the intersection of their kernels, and let $\mathrm{ribbonGram}\,D_i$ be the restriction to it of the pairing $\langle x,y\rangle=\sum_{e}w_i(e)\,x(e)y(e)$, viewed as a map into the $\mathbb{Z}$-dual. Let $H_i$ be Hecke data for $D_i$: commuting families of integral matrices $T_i(\ell)$ on $E_i$ and $T_{i,V}(\ell)$ on $V_i$ indexed by the primes, a finite exceptional set, equivariance of $\delta_i^j$ for primes outside it, and stability of the ribbon kernel under every $T_i(\ell)$. Let $M$ be a matching of $H_1$ with $H_2$: bijections $E_1\simeq E_2$, $V_1\simeq V_2$ compatible with $a$, $b$ and $w$, plus a finite set of bad primes, with $T(\ell)$ intertwined by transport of functions for good primes and intertwined on the ribbon kernel for bad ones. Then there exists a $\mathbb{Z}$-linear isomorphism $e\colon \mathrm{ribbonKernel}\,D_1\to\mathrm{ribbonKernel}\,D_2$ commuting with the restricted operators $\mathrm{heckeKernelMap}\,H_i\,\ell$ for every prime $\ell$, and satisfying $\mathrm{ribbonGram}\,D_2(e\,x)(e\,y)=\mathrm{ribbonGram}\,D_1(x)(y)$ for all $x,y$.
--
--   This is the combinatorial transport step in the Cerednik–Drinfeld style comparison of the character-group data attached to two places: matched degeneracy and Hecke configurations have ribbon kernels that agree as Hecke modules equipped with their width pairings. It is used by [`CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_matching`](thm.html#CerednikDrinfeld.TwoPlaceTorsionDatum.exists_laws_of_matching) to produce the pairing and Hecke laws on the torsion datum at two places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ribbon_kernelEquiv.lean

import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_CerednikDrinfeld_Ribbon
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Finiteness.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve
universe u_1 u_2 u_3 u_4

theorem CerednikDrinfeld.ribbon_kernelEquiv :
    ∀ {E₁ : Type u_1} {V₁ : Type u_2} {E₂ : Type u_3} {V₂ : Type u_4}
  [inst : Fintype E₁] [inst_1 : Fintype V₁] [inst_2 : DecidableEq V₁] [inst_3 : Fintype E₂] [inst_4 : Fintype V₂]
  [inst_5 : DecidableEq V₂] {D₁ : CerednikDrinfeld.DegeneracyData E₁ V₁} {D₂ : CerednikDrinfeld.DegeneracyData E₂ V₂}
  (H₁ : CerednikDrinfeld.HeckeData D₁) (H₂ : CerednikDrinfeld.HeckeData D₂) (M : CerednikDrinfeld.Matching H₁ H₂),
  ∃ (e : ↥(CerednikDrinfeld.ribbonKernel D₁) ≃ₗ[ℤ] ↥(CerednikDrinfeld.ribbonKernel D₂)),
    (∀ (ℓ : Nat.Primes) (x : ↥(CerednikDrinfeld.ribbonKernel D₁)),
        e ((CerednikDrinfeld.heckeKernelMap H₁ ℓ) x) = (CerednikDrinfeld.heckeKernelMap H₂ ℓ) (e x)) ∧
      ∀ (x y : ↥(CerednikDrinfeld.ribbonKernel D₁)),
        ((CerednikDrinfeld.ribbonGram D₂) (e x)) (e y) = ((CerednikDrinfeld.ribbonGram D₁) x) y := by sorry
