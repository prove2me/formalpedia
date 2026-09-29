-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_PeriodDatum_comp_pushforward_mem_periodLattice_of_forall_eq
-- name    : CerednikDrinfeld.Mumford.PeriodDatum.comp_pushforward_mem_periodLattice_of_forall_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/edf0263f-2420-5f2d-99b0-2fc404b916a8
-- title:
--   Period lattices are natural along a finite harmonic morphism
-- statement:
--   Fix finite edge and vertex sets $E_1,V_1,E_2,V_2$ and degeneracy data $D_1$ on $(E_1,V_1)$ and $D_2$ on $(E_2,V_2)$, each consisting of two maps $a,b\colon E\to V$ and a width function $w\colon E\to\mathbb{N}_{>0}$, and let $\mu\colon D_1\to D_2$ be a finite homomorphism, i.e. maps $\mathrm{mapV},\mathrm{mapE}$ compatible with $a$, $b$, together with edge, vertex and total degrees satisfying the width and fibre-sum conditions; $\mu$ induces $\mu_*$ on the ribbon kernels (the intersection of the kernels of push-forward along $a$ and along $b$ inside $E\to\mathbb{Z}$) and $\mu^*$ given by $(\mu^*y)(e)=\deg(e)\,y(\mathrm{mapE}\,e)$. Let $K_1,K_2,L$ be fields with $L$ an algebra over each, let $\mathrm{ord}_i\colon \mathrm{Additive}\,K_i^\times\to\mathbb{Z}$ be additive maps, and let $P_i$ be period data for $D_i$ over $(K_i,L,\mathrm{ord}_i)$, so each carries a symmetric $\mathbb{Z}$-bilinear pairing $Q_i$ on the ribbon kernel with values in $\mathrm{Additive}\,K_i^\times$ whose $\mathrm{ord}_i$ is the ribbon Gram pairing. Assume the projection formula: for all $x$ in the ribbon kernel of $D_2$ and $y$ in that of $D_1$, the images in $L$ of $Q_1(\mu^*x,y)$ and $Q_2(x,\mu_*y)$ agree. Then for every torus point $u\colon \mathrm{ribbonKernel}\,D_2\to\mathrm{Additive}\,L^\times$ lying in the period lattice of $P_2$ (the range of the $L$-valued pairing map of $P_2$), the composite $u\circ\mu_*$ lies in the period lattice of $P_1$.
--
--   This is the lattice half of the conorm compatibility for Mumford-uniformised Jacobians along a finite morphism of totally degenerate curves: a torus point arising as a period of $D_2$ pulls back, along push-forward of ribbon cycles, to a period of $D_1$. It is used in the construction of the conorm square for the family of equivariant uniformisations of Mumford quotients in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_PeriodDatum_comp_pushforward_mem_periodLattice_of_forall_eq.lean

import Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford AlgebraicCurve

theorem CerednikDrinfeld.Mumford.PeriodDatum.comp_pushforward_mem_periodLattice_of_forall_eq
    {E₁ V₁ E₂ V₂ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq E₁] [DecidableEq V₁]
    [Fintype E₂] [Fintype V₂] [DecidableEq E₂] [DecidableEq V₂]
    {D₁ : DegeneracyData E₁ V₁} {D₂ : DegeneracyData E₂ V₂} (μ : D₁.FiniteHom D₂)
    {K₁ K₂ L : Type} [Field K₁] [Field K₂] [Field L] [Algebra K₁ L] [Algebra K₂ L]
    {ord₁ : Additive K₁ˣ →+ ℤ} {ord₂ : Additive K₂ˣ →+ ℤ}
    (P₁ : PeriodDatum D₁ K₁ L ord₁) (P₂ : PeriodDatum D₂ K₂ L ord₂)
    (hproj : ∀ (x : ↥(ribbonKernel D₂)) (y : ↥(ribbonKernel D₁)),
      algebraMap K₁ L (((Additive.toMul (P₁.Q (μ.pullback x) y)) : K₁ˣ) : K₁) =
        algebraMap K₂ L (((Additive.toMul (P₂.Q x (μ.pushforward y))) : K₂ˣ) : K₂))
    (u : P₂.TorusPoints) (hu : u ∈ P₂.periodLattice) :
    u.comp μ.pushforward ∈ P₁.periodLattice := by sorry
