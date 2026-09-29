-- Prove2me | Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_pullback_eq_unitPullback
-- name    : AlgebraicGeometry.SmallExtension.exists_isPicObstructionCocycle_pullback_eq_unitPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.655938+00:00
-- url     : https://prove2.me/theorems/73e9c55b-2767-5660-8e97-b3b45e780e5f
-- title:
--   Naturality of Picard obstruction cocycles under refinement
-- statement:
--   Let $B_1$ be a commutative ring, $k$ a field, $V$ a $k$-module which is also a $B_1$-module, and $\iota\colon V\to B_1$ a $B_1$-linear map whose image multiplies to zero, $\iota(v)\iota(w)=0$ for all $v,w\in V$. Let $f\colon X\to\operatorname{Spec}B_1$ and $f'\colon X'\to\operatorname{Spec}B_1$, let $g\colon X_0\to X$, $g'\colon X_0'\to X'$, $i\colon X_k\to X$, $i'\colon X_k'\to X'$ be affine morphisms, and $f_k\colon X_k\to\operatorname{Spec}k$, $f_k'\colon X_k'\to\operatorname{Spec}k$. Let $h\colon X'\to X$ satisfy $f'=f\circ h$, and let $h_0\colon X_0'\to X_0$, $h_k\colon X_k'\to X_k$ satisfy $g\circ h_0=h\circ g'$, $i\circ h_k=h\circ i'$ and $f_k'=f_k\circ h_k$. Let $\mathcal U$ be a finite linearly ordered affine open cover of $X$ and $\mathcal W$ one of $X'$, together with $\lambda\colon\mathcal W.\iota\to\mathcal U.\iota$ such that $\mathcal W.U(w)\le h^{-1}\mathcal U.U(\lambda w)$ and, for the preimage covers, $i'^{-1}\mathcal W.U(w)\le h_k^{-1}i^{-1}\mathcal U.U(\lambda w)$. Finally let $\mathcal L_0$ be a module on $X_0$ and $c$ a $k$-linear map from $\mathrm{Dual}_k V$ to the $2$-cochains of the structure-sheaf presheaf of $f_k$ on the cover $i^{-1}\mathcal U$, satisfying `IsPicObstructionCocycle`: there are a Čech trivialisation $\tau$ of $\mathcal L_0$ on $g^{-1}\mathcal U$ and sections $u_s,u'_s$ on each double intersection $\mathcal U.\mathrm{inter}(s)$ with $g^\sharp u_s$ restricting to the transition function $\tau_s$, with $u_su'_s=1$, and such that for every strictly increasing triple $r$ the defect $u_{\mathrm{face}(r,2)}u_{\mathrm{face}(r,0)}u'_{\mathrm{face}(r,1)}-1$ (restricted to $\mathcal U.\mathrm{inter}(r)$) is a fibre reading of the component $c(\cdot)_r$, i.e. equals $\sum_j\iota(v_j)s_j$ for finitely many $v_j\in V$, $s_j\in\Gamma(X,\mathcal U.\mathrm{inter}(r))$ with $c(\xi)_r=\sum_j\xi(v_j)\,i^\sharp s_j$ restricted to $(i^{-1}\mathcal U).\mathrm{inter}(r)$. The conclusion is that there exists a $k$-linear $c'$ from $\mathrm{Dual}_k V$ to the $2$-cochains of the structure-sheaf presheaf of $f_k'$ on $i'^{-1}\mathcal W$ such that, for every $\xi$, $c'(\xi)$ is exactly the signed alternating refinement pull-back `OModulePresheaf.unitPullback` of $c(\xi)$ along $h_k$ through $\lambda$ (on a triple $s$: the sign of the permutation sorting $\lambda\circ s$ times $h_k^\sharp$ of the component at the sorted triple when $\lambda\circ s$ is injective, and $0$ otherwise), and such that $c'$ satisfies `IsPicObstructionCocycle` for $f'$, $f_k'$, $i'$, $g'$, the cover $\mathcal W$ and the pull-back module $h_0^*\mathcal L_0$.
--
--   This is the functoriality of the Čech–Picard obstruction at the level of cochains, not merely of cohomology classes: a Picard obstruction cocycle for a module on the first-order thickening transports along a morphism of thickened schemes and a refinement of the chosen ordered affine covers, and the transport is given by the signed alternating refinement pull-back on the nose. It is used in the computation of the obstruction attached to Mumford bundles and in the Rosati-compatibility comparison for fake elliptic curves in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SmallExtension_exists_isPicObstructionCocycle_pullback_eq_unitPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension
  Scheme.TwoAffineOpenCover

universe u

theorem AlgebraicGeometry.SmallExtension.exists_isPicObstructionCocycle_pullback_eq_unitPullback
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    (hJ : ∀ v w : V, ι v * ι w = 0)
    {X X' X₀ X₀' Xk Xk' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B₁)) (f' : X' ⟶ Spec (CommRingCat.of B₁))
    (g : X₀ ⟶ X) [IsAffineHom g] (g' : X₀' ⟶ X') [IsAffineHom g']
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (fk' : Xk' ⟶ Spec (CommRingCat.of k))
    (i : Xk ⟶ X) [IsAffineHom i] (i' : Xk' ⟶ X') [IsAffineHom i']

    (h : X' ⟶ X) (hh : h ≫ f = f')
    (h₀ : X₀' ⟶ X₀) (hh₀ : h₀ ≫ g = g' ≫ h)
    (hk : Xk' ⟶ Xk) (hhk : hk ≫ i = i' ≫ h) (hfk : hk ≫ fk = fk')

    (𝒰 : X.OrderedAffineCover) (𝒲 : X'.OrderedAffineCover) (lam : 𝒲.ι → 𝒰.ι)
    (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒰.U (lam w))
    (hlamk : ∀ w, (𝒲.comap i').U w ≤ hk ⁻¹ᵁ (𝒰.comap i).U (lam w))
    (𝓛₀ : X₀.Modules) (c : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2)
    (hc : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c) :
    ∃ c' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').cochain (𝒲.comap i') 2,
      (∀ ξ : Module.Dual k V,
        c' ξ = OModulePresheaf.unitPullback (πX := fk') hk (𝒲.comap i') (𝒰.comap i) lam hlamk 2 (c ξ)) ∧
      IsPicObstructionCocycle V ι f' fk' i' g' 𝒲 ((Scheme.Modules.pullback h₀).obj 𝓛₀) c' := by sorry
