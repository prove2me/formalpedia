-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_comp_pullback_mem_periodLattice_of_forall_eq
-- name    : CerednikDrinfeld.Mumford.PeriodDatum.comp_pullback_mem_periodLattice_of_forall_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/24231aa6-643e-5a9e-81c2-84629c7cfc4e
-- title:
--   Naturality of period lattices under pullback along μ
-- statement:
--   Let $E_1,V_1,E_2,V_2$ be finite types with decidable equality, and let $D_1$ be a degeneracy datum on $(E_1,V_1)$ and $D_2$ one on $(E_2,V_2)$, each consisting of two maps $a,b\colon E\to V$ and a width function $w\colon E\to\mathbb{Z}_{>0}$. Let $\mu\colon D_1\to D_2$ be a finite homomorphism, i.e. maps $\mathrm{mapV}\colon V_1\to V_2$, $\mathrm{mapE}\colon E_1\to E_2$ compatible with $a$ and $b$, together with local degrees $\deg$, $\deg_V$ and a total degree satisfying $w_2(\mathrm{mapE}\,e)=\deg(e)\,w_1(e)$ and the fibrewise summation conditions. Let $K_1,K_2,L$ be fields with algebra maps $K_i\to L$, let $\mathrm{ord}_i\colon \mathrm{Additive}\,K_i^\times\to\mathbb{Z}$ be additive maps, and let $P_i$ be a period datum on $D_i$ over $(K_i,L,\mathrm{ord}_i)$, i.e. a symmetric $\mathbb{Z}$-bilinear pairing $Q_i$ on the ribbon kernel of $D_i$ (the intersection of the kernels of pushforward along $a$ and along $b$) with values in $\mathrm{Additive}\,K_i^\times$, whose $\mathrm{ord}_i$ computes the ribbon Gram pairing. Assume the projection formula: for all $x$ in the ribbon kernel of $D_2$ and $y$ in that of $D_1$, the images in $L$ of $Q_1(\mu^{*}x,y)$ and $Q_2(x,\mu_{*}y)$ agree, where $\mu^{*}$ is pullback, $(\mu^{*}x)(e)=\deg(e)\,x(\mathrm{mapE}\,e)$, and $\mu_{*}$ is pushforward along $\mathrm{mapE}$. Then for any torus point $u'$, i.e. a $\mathbb{Z}$-linear map from the ribbon kernel of $D_1$ to $\mathrm{Additive}\,L^\times$, lying in $P_1$'s period lattice (the range of `P₁.QL`), the composite $\mu^{*}$ followed by $u'$ lies in $P_2$'s period lattice.
--
--   This is the lattice half of the compatibility of Mumford-style uniformisations of Jacobians with a finite morphism: pullback of cycles carries periods of the source to periods of the target, once the projection formula between the two period pairings is known. It is used in the comparison of theta-type divisor classes for Mumford quotients, through [`AlgebraicCurve.Pic0.eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta`](thm.html#AlgebraicCurve.Pic0.eFull_comp_pullback_eq_mk_pushforwardAlong_of_mumfordQuotient_theta).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_PeriodDatum_comp_pullback_mem_periodLattice_of_forall_eq.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Mumford.PeriodDatum.comp_pullback_mem_periodLattice_of_forall_eq
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq E₁] [DecidableEq V₁]
    [Fintype E₂] [Fintype V₂] [DecidableEq E₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂} (μ : D₁.FiniteHom D₂)
    {K₁ K₂ L : Type} [Field K₁] [Field K₂] [Field L] [Algebra K₁ L] [Algebra K₂ L]
    {ord₁ : Additive K₁ˣ →+ ℤ} {ord₂ : Additive K₂ˣ →+ ℤ}
    (P₁ : PeriodDatum D₁ K₁ L ord₁) (P₂ : PeriodDatum D₂ K₂ L ord₂)
    (hproj : ∀ (x : ↥(ribbonKernel D₂)) (y : ↥(ribbonKernel D₁)),
      algebraMap K₁ L (((Additive.toMul (P₁.Q (μ.pullback x) y)) : K₁ˣ) : K₁) =
        algebraMap K₂ L (((Additive.toMul (P₂.Q x (μ.pushforward y))) : K₂ˣ) : K₂))
    (u' : P₁.TorusPoints) (hu' : u' ∈ P₁.periodLattice) :
    u'.comp μ.pullback ∈ P₂.periodLattice := by sorry
