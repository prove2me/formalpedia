-- Prove2me | Theorems.Thm_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities
-- name    : CohCarrier.HeckeData.exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/f44bfc37-73a7-55d1-a8cf-caac5cc61b24
-- title:
--   Abstract α-stabilisation from degeneracy and Atkin–Lehner identities
-- statement:
--   Let $\mathcal O$ be a commutative noetherian local ring, complete with respect to its maximal ideal, let $k$ be a field that is an $\mathcal O$-algebra with $\mathcal O \to k$ surjective, and let $V$, $W$ be $\mathcal O$-modules with $V$ finite over $\mathcal O$. Let `DV`, `DW` be Hecke data for $V$, $W$ with values in $k$, i.e. index types `DV.Gen`, `DW.Gen`, families of pairwise commuting $\mathcal O$-endomorphisms `DV.op`, `DW.op`, and functions `DV.θbar`, `DW.θbar` to $k$. Suppose the generator sets are identified with $G \sqcup \{*\}$ by bijections $\sigma_V$, $\sigma_W$; write $X_g, T$ and $Y_g, U$ for the operators indexed by $g \in G$ and by $*$ on $V$ and on $W$, and assume `DW.θbar` and `DV.θbar` agree on the $G$-part. Let $\iota : V \to W$, $j : W \to V$ be $\mathcal O$-linear, $w$ an $\mathcal O$-endomorphism of $W$, with $\iota X_g = Y_g \iota$, $j Y_g = X_g j$ and $w Y_g = Y_g w$ for all $g$. Let $q \in \mathbb N$ and $d \in G$ with $X_d$ and $Y_d$ invertible, and assume $w\iota = (\iota T - U\iota)X_d$, $j\iota = (q+1)\,\mathrm{id}$, $j w \iota = T X_d$, $\iota j = \mathrm{id} + U w$, $w^2 = Y_d$. Assume further $q = 1$ in $k$, `DV.θbar` at $d$ equals $1$, and that $\alpha, \beta \in k$ satisfy `DW.θbar` at $*$ $= \alpha$, `DV.θbar` at $*$ $= \alpha + \beta$, $\alpha\beta = 1$ and $\alpha \neq \beta$. Then there is an $\mathcal O$-linear isomorphism $e$ from `DW.ML` to `DV.ML` such that for every $g \in G$ and every $x$, $e$ carries the action on `DW.ML` of the polynomial variable indexed by $\sigma_W(g)$ in `DW.FreeAlg` $= \mathcal O[\,$`DW.Gen`$\,]$ to the action of the variable indexed by $\sigma_V(g)$ in `DV.FreeAlg`.
--
--   This is the abstract form of $\alpha$-stabilisation at a single auxiliary (Taylor–Wiles) prime: the five degeneracy and Atkin–Lehner identities, together with the residual conditions $q \equiv 1$, $\alpha\beta = 1$, $\alpha \neq \beta$, force the localisation of the higher-level module $W$ where the operator $U$ has residual eigenvalue $\alpha$ to be isomorphic, compatibly with the operators indexed by $G$, to the localisation of $V$ where $T$ has residual eigenvalue $\alpha + \beta$. It is obtained from the companion-matrix comparison [`CohCarrier.HeckeData.exists_linearEquiv_ML_prod_of_companion`](thm.html#CohCarrier.HeckeData.exists_linearEquiv_ML_prod_of_companion), and is used for the level-raising comparison of cusp forms at a Taylor–Wiles level in [`CuspForm.TWLevel.exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq`](thm.html#CuspForm.TWLevel.exists_linearEquiv_ML_HR_init_of_toML_diamondL_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_HeckeData_exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities.lean

import Mathlib
import Definitions.Def_CohCarrier_HeckeData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
attribute [local instance] CohCarrier.HeckeData.moduleFreeAlg

open CohCarrier

theorem CohCarrier.HeckeData.exists_linearEquiv_ML_of_degeneracy_atkinLehner_identities
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] [IsNoetherianRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    {k : Type} [Field k] [Algebra 𝒪 k] (hk : Function.Surjective (algebraMap 𝒪 k))

    {V W : Type} [AddCommGroup V] [Module 𝒪 V] [Module.Finite 𝒪 V] [AddCommGroup W] [Module 𝒪 W]
    (DV : HeckeData 𝒪 V k) (DW : HeckeData 𝒪 W k)

    {G : Type} (σV : G ⊕ Unit ≃ DV.Gen) (σW : G ⊕ Unit ≃ DW.Gen)
    (hθ : ∀ g : G, DW.θbar (σW (Sum.inl g)) = DV.θbar (σV (Sum.inl g)))

    (ι : V →ₗ[𝒪] W) (j : W →ₗ[𝒪] V) (w : Module.End 𝒪 W)
    (hι : ∀ g : G, ι ∘ₗ DV.op (σV (Sum.inl g)) = DW.op (σW (Sum.inl g)) ∘ₗ ι)
    (hj : ∀ g : G, j ∘ₗ DW.op (σW (Sum.inl g)) = DV.op (σV (Sum.inl g)) ∘ₗ j)
    (hw : ∀ g : G, w * DW.op (σW (Sum.inl g)) = DW.op (σW (Sum.inl g)) * w)

    (q : ℕ) (d : G) (hdV : IsUnit (DV.op (σV (Sum.inl d)))) (hdW : IsUnit (DW.op (σW (Sum.inl d))))

    (h₁ : w ∘ₗ ι = (ι ∘ₗ DV.op (σV (Sum.inr ())) - DW.op (σW (Sum.inr ())) ∘ₗ ι) ∘ₗ
      DV.op (σV (Sum.inl d)))
    (h₂ : j ∘ₗ ι = ((q : 𝒪) + 1) • LinearMap.id)
    (h₃ : j ∘ₗ w ∘ₗ ι = DV.op (σV (Sum.inr ())) * DV.op (σV (Sum.inl d)))
    (h₄ : ι ∘ₗ j = LinearMap.id + DW.op (σW (Sum.inr ())) * w)
    (h₅ : w * w = DW.op (σW (Sum.inl d)))

    (hq : (q : k) = 1) (hd : DV.θbar (σV (Sum.inl d)) = 1)
    (α β : k) (hα : DW.θbar (σW (Sum.inr ())) = α) (hT : DV.θbar (σV (Sum.inr ())) = α + β)
    (hαβ : α * β = 1) (hne : α ≠ β) :
    ∃ e : DW.ML ≃ₗ[𝒪] DV.ML, ∀ (g : G) (x : DW.ML),
      e ((MvPolynomial.X (σW (Sum.inl g)) : DW.FreeAlg) • x) =
        (MvPolynomial.X (σV (Sum.inl g)) : DV.FreeAlg) • e x := by sorry
