-- Prove2me | Theorems.Thm_CohCarrier_HeckeData_exists_linearEquiv_ML_prod_of_companion
-- name    : CohCarrier.HeckeData.exists_linearEquiv_ML_prod_of_companion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/1ef4f978-4ac1-5f28-af71-290fd49ef3a6
-- title:
--   Hensel splitting of a companion module at a simple root
-- statement:
--   Let $\mathcal O$ be a commutative noetherian local ring, complete for the adic topology of its maximal ideal, let $k$ be a field carrying an $\mathcal O$-algebra structure whose structure map is surjective, and let $V$ be a finitely generated $\mathcal O$-module. Let $DV$ be Hecke data for $V$ over $k$ and $DP$ Hecke data for $V \times V$ over $k$; such data consist of a type of generators, a family `op` of pairwise commuting $\mathcal O$-endomorphisms of the module indexed by that type, and residual values `θbar` of the generators in $k$. Assume the generator sets are indexed by $G \sqcup \{*\}$, via bijections $\sigma_V$ and $\sigma_P$, that the residual values of corresponding generators indexed by $G$ agree, and fix $c \in \mathcal O$, $d \in G$ and an endomorphism $D^{-1}$ of $V$ that is a two-sided inverse of $DV.\mathrm{op}(\sigma_V(d))$. Assume further that for $g \in G$ the operator $DP.\mathrm{op}(\sigma_P(g))$ is the diagonal map $DV.\mathrm{op}(\sigma_V(g)) \times DV.\mathrm{op}(\sigma_V(g))$, and that the extra generator of $DP$ acts by the companion operator $(x,y) \mapsto (Tx + cy,\, -D^{-1}x)$, where $T = DV.\mathrm{op}(\sigma_V(*))$. Finally let $\alpha, \beta \in k$ with $DP.\bar\theta(\sigma_P(*)) = \alpha$, $DV.\bar\theta(\sigma_V(*)) = \alpha + \beta$, $\alpha\beta \cdot DV.\bar\theta(\sigma_V(d))$ equal to the image of $c$ in $k$, that image nonzero, and $\alpha \neq \beta$. The conclusion is that there exists an $\mathcal O$-linear isomorphism $e : DP.\mathrm{ML} \simeq DV.\mathrm{ML}$ between the associated modules which, for every $g \in G$, intertwines the action of the polynomial variable $X_{\sigma_P(g)}$ of $DP.\mathrm{FreeAlg} = \mathcal O[X_h : h \in DP.\mathrm{Gen}]$ with that of $X_{\sigma_V(g)}$; no compatibility at the extra generator is asserted.
--
--   This is the module-theoretic form of $\alpha$-stabilisation: splitting the plane $V \times V$, on which a companion operator of the quadratic $X^2 - TX + cD^{-1}$ acts, at the simple residual root $\alpha$, and identifying the resulting piece equivariantly for the remaining commuting operators with $V$ localised at $T \mapsto \alpha + \beta$. It is used in [`CohCarrier.HeckeData.exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities`](thm.html#CohCarrier.HeckeData.exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities), in the comparison at a Taylor–Wiles prime between the old part of cohomology at the raised level and cohomology at the original level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_HeckeData_exists_linearEquiv_ML_prod_of_companion.lean

import Mathlib
import Definitions.Def_CohCarrier_HeckeData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

open CohCarrier

theorem CohCarrier.HeckeData.exists_linearEquiv_ML_prod_of_companion
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V]

    (DV : HeckeData 𝒪 V k) (DP : HeckeData 𝒪 (V × V) k)

    {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σP : G ⊕ Unit ≃ DP.Gen)
    (hθ : ∀ g : G, DP.θbar (σP (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))

    (c : 𝒪) (d : G) (Dinv : Module.End 𝒪 V)
    (hDinv : DV.op (σV (Sum.inl d)) * Dinv = 1) (hDinv' : Dinv * DV.op (σV (Sum.inl d)) = 1)

    (hop_inl : ∀ g : G,
      DP.op (σP (Sum.inl g)) = (DV.op (σV (Sum.inl g))).prodMap (DV.op (σV (Sum.inl g))))
    (hop_inr : DP.op (σP (Sum.inr ())) =
      (DV.op (σV (Sum.inr ())) ∘ₗ LinearMap.fst 𝒪 V V + c • LinearMap.snd 𝒪 V V).prod
        (-(Dinv ∘ₗ LinearMap.fst 𝒪 V V)))

    (α β : k) (hα : DP.θbar (σP (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
    (hprod : α * β * DV.θbar (σV (Sum.inl d)) = algebraMap 𝒪 k c) (hc : algebraMap 𝒪 k c ≠ 0)
    (hne : α ≠ β) :
    ∃ e : DP.ML ≃ₗ[𝒪] DV.ML, ∀ (g : G) (x : DP.ML),
      e ((MvPolynomial.X (σP (Sum.inl g)) : DP.FreeAlg) • x) =
        (MvPolynomial.X (σV (Sum.inl g)) : DV.FreeAlg) • e x := by sorry
