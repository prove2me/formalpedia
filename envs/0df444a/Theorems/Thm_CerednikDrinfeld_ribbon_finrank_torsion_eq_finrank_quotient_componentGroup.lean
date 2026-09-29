-- Prove2me | Theorems.Thm_CerednikDrinfeld_ribbon_finrank_torsion_eq_finrank_quotient_componentGroup
-- name    : CerednikDrinfeld.ribbon_finrank_torsion_eq_finrank_quotient_componentGroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/01a7c3e2-d63e-56ea-b9f5-5da368a0c3e2
-- title:
--   Component-group duality: dim_k Ψ[𝔪]=dim_k Ψ^{dagger}/𝔪Ψ^{dagger}
-- statement:
--   Let $E$ and $V$ be finite types and let $D$ be a degeneracy datum on them, that is, two maps $a,b:E\to V$ and a weight function $w:E\to\mathbb{N}^{+}$. Write $Y=\mathrm{ribbonKernel}\,D$ for the intersection of the kernels of the two pushforward maps $(E\to\mathbb{Z})\to(V\to\mathbb{Z})$ along $a$ and $b$, let $\langle x,y\rangle=\sum_{e}w_e\,x_e y_e$ be the weighted pairing restricted to $Y$, viewed as a map $\mathrm{ribbonGram}\,D:Y\to\mathrm{Hom}_{\mathbb{Z}}(Y,\mathbb{Z})$, and let $\Psi=\mathrm{ribbonComponentGroup}\,D$ be the quotient of $\mathrm{Hom}_{\mathbb{Z}}(Y,\mathbb{Z})$ by the image of this map. Let $H$ be a Hecke datum for $D$: commuting integer matrices $T_\ell$ on $E$ and $T_\ell^{V}$ on $V$ indexed by the primes, a finite exceptional set $S$ outside of which the two pushforwards intertwine $T_\ell$ with $T_\ell^{V}$, and stability of $Y$ under every $T_\ell$; write $\mathrm{heckeKernelMap}\,H\,\ell$ for the induced endomorphism of $Y$. Let $\mathrm{Tadj}$ assign to each prime $\ell$ an endomorphism $T_\ell^{\dagger}$ of $Y$, and assume both adjointness relations $\langle T_\ell^{\dagger}x,y\rangle=\langle x,T_\ell y\rangle$ and $\langle T_\ell x,y\rangle=\langle x,T_\ell^{\dagger}y\rangle$ for all $x,y\in Y$. Let $\mathbb{T}=\mathrm{HeckeAlg}$ be the polynomial ring $\mathbb{Z}[X_\ell:\ell\text{ prime}]$ with generators $\mathrm{heckeGen}\,\ell=X_\ell$. Let $\Psi^{\mathrm{mod}}$ be a $\mathbb{T}$-module together with an additive isomorphism $e_{\Psi}:\Psi^{\mathrm{mod}}\simeq\Psi$ transporting the action of $X_\ell$ to the endomorphism of $\Psi$ induced by the dual of $\mathrm{heckeKernelMap}\,H\,\ell$ (well defined by the first adjointness relation), and let $\Psi^{\dagger\mathrm{mod}}$ be a $\mathbb{T}$-module with an additive isomorphism $e_{\Psi}^{\dagger}:\Psi^{\dagger\mathrm{mod}}\simeq\Psi$ transporting the action of $X_\ell$ to the endomorphism of $\Psi$ induced by the dual of $T_\ell^{\dagger}$ (well defined by the second relation). Then for every maximal ideal $\mathfrak{m}$ of $\mathbb{T}$, with residue field $k=\mathbb{T}/\mathfrak{m}$, the $k$-dimension of the submodule of $\Psi^{\mathrm{mod}}$ annihilated by all of $\mathfrak{m}$ equals the $k$-dimension of $\Psi^{\dagger\mathrm{mod}}/\mathfrak{m}\,\Psi^{\dagger\mathrm{mod}}$.
--
--   This is the Hecke-equivariant duality for the component group of a toric degeneration presented combinatorially: $\Psi=Y^{*}/\iota(Y)$ for the monodromy pairing $\iota$ on the character lattice $Y$, with the action induced by $T_\ell$ adjoint to the action induced by $T_\ell^{\dagger}$, so that the $\mathfrak{m}$-torsion of one transported module and the $\mathfrak{m}$-cotorsion of the other have equal dimension over the residue field. It is used, via the Čerednik–Drinfeld description of the component group of a Shimura curve Jacobian, in the comparison of component groups with character lattices for supersingular level data that feeds into level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ribbon_finrank_torsion_eq_finrank_quotient_componentGroup.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem CerednikDrinfeld.ribbon_finrank_torsion_eq_finrank_quotient_componentGroup
    {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}
    (H : HeckeData D)
    (Tadj : Nat.Primes → (ribbonKernel D →ₗ[ℤ] ribbonKernel D))
    (hadjK : ∀ (ℓ : Nat.Primes) (x y : ribbonKernel D),
      ribbonGram D (Tadj ℓ x) y = ribbonGram D x (heckeKernelMap H ℓ y))
    (hadjK' : ∀ (ℓ : Nat.Primes) (x y : ribbonKernel D),
      ribbonGram D (heckeKernelMap H ℓ x) y = ribbonGram D x (Tadj ℓ y))
    {Ψmod : Type*} [AddCommGroup Ψmod] [Module HeckeAlg Ψmod]
    (eΨ : Ψmod ≃+ ribbonComponentGroup D)
    (hΨ : ∀ (ℓ : Nat.Primes) (c : Ψmod), eΨ (heckeGen ℓ • c) =
      ribbonComponentGroupMap D (Tadj ℓ) (heckeKernelMap H ℓ) (hadjK ℓ) (eΨ c))
    {Ψamod : Type*} [AddCommGroup Ψamod] [Module HeckeAlg Ψamod]
    (eΨa : Ψamod ≃+ ribbonComponentGroup D)
    (hΨa : ∀ (ℓ : Nat.Primes) (c : Ψamod), eΨa (heckeGen ℓ • c) =
      ribbonComponentGroupMap D (heckeKernelMap H ℓ) (Tadj ℓ) (hadjK' ℓ) (eΨa c))
    (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal] :
    Module.finrank (HeckeAlg ⧸ 𝔪) ↥(heckeTorsion Ψmod 𝔪) =
      Module.finrank (HeckeAlg ⧸ 𝔪) (Ψamod ⧸ (𝔪 • (⊤ : Submodule HeckeAlg Ψamod))) := by sorry
