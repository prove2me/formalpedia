-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates
-- name    : AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/8ccf47a3-b42e-5193-a9fe-13655cc55a1d
-- title:
--   Dévissage along the mathcal I_Y-adic filtration
-- statement:
--   Let $R$ be a Noetherian commutative ring, let $V$ be a scheme with a proper morphism $\pi : V \to \operatorname{Spec} R$, let $Y$ be a closed subset of $V$, and let $Q$ be a predicate on the type `OModulePresheaf π` of presheaves of modules on $V$ over $\pi$ — data assigning to each open $U$ an $R$-module that is also a $\Gamma(V,U)$-module compatibly with the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with functorial $R$-linear restriction maps semilinear over restriction of sections. Assume: (h0) $Q(G)$ holds for every $G$ whose module of sections over each affine open of $V$ is a subsingleton; (hext) for any $G_1,G_2,G_3$ admitting a nonempty `AffSES`, i.e. maps $G_1 \to G_2 \to G_3$ given over each affine open by $\Gamma(V,U)$-linear maps commuting with restriction along inclusions of affine opens, with the first injective, the second surjective and the range of the first equal to the kernel of the second on every affine open, all three of $G_1,G_2,G_3$ being coherent (finitely generated sections over each affine open) and quasi-coherent (over each affine open $U$ and each $f \in \Gamma(V,U)$, every section over $V.\mathrm{basicOpen}\,f$ becomes the restriction of a section over $U$ after multiplication by a power of $f$, and any section over $U$ restricting to $0$ there is killed by a power of $f$), each of $Q(G_1),Q(G_3)$, $Q(G_1),Q(G_2)$, $Q(G_2),Q(G_3)$ implies respectively $Q(G_2)$, $Q(G_3)$, $Q(G_1)$; (hann) $Q(G)$ holds for every coherent quasi-coherent $G$ supported in $Y$ (sections subsingleton over affine opens disjoint from $Y$) all of whose sections over an affine open $U$ are annihilated by every element of the ideal at $U$ of the vanishing ideal sheaf data of $Y$. Then $Q(F)$ holds for every coherent quasi-coherent $F$ supported in $Y$.
--
--   This is the first step of Grothendieck's dévissage, reducing a two-out-of-three property of coherent quasi-coherent module data supported in a closed set $Y$ to the case of data annihilated by the ideal of $Y$, by climbing the $\mathcal I_Y$-adic filtration, which terminates because some power of $\mathcal I_Y$ annihilates the data on each affine open. It feeds the reduction of statements about coherent data to data over integral closed subschemes used in [`AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_forall_of_forall_idealAnnihilates.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (Y : Closeds V) (Q : OModulePresheaf π → Prop)
    (h0 : ∀ G : OModulePresheaf π, (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q G)
    (hext : ∀ (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃) →
      G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
      G₃.IsCoherent → G₃.IsQuasicoherent →
      (Q G₁ → Q G₃ → Q G₂) ∧ (Q G₁ → Q G₂ → Q G₃) ∧ (Q G₂ → Q G₃ → Q G₁))
    (hann : ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y →
      OModulePresheaf.IdealAnnihilates π (Scheme.IdealSheafData.vanishingIdeal Y) G → Q G) :
    ∀ F : OModulePresheaf π, F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → Q F := by sorry
