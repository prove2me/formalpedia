-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer
-- name    : CerednikDrinfeld.Mumford.finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/7174314c-adef-5fc1-9bbb-1eee09a3a81a
-- title:
--   Pull-back of quotient-graph cycles equals transfer
-- statement:
--   Let a group $G$ act on a type $W$ carrying a simple graph $\mathcal T$ so that every $g \in G$ sends adjacent vertices to adjacent vertices, assume $\mathcal T$ is a tree and every vertex stabiliser in $G$ is finite, and let $\tau : W \to \mathbb Z/2$ be a $G$-invariant function taking distinct values on adjacent vertices. Let $\Gamma' \le G$ be of finite index, again acting on $\mathcal T$ by graph automorphisms. Let $D_1$ be a degeneracy datum on a finite edge set $E_1$ and vertex set $V_1$, i.e. maps $a, b : E_1 \to V_1$ and widths $w : E_1 \to \mathbb Z_{>0}$, together with a bijection $eE_1$ of $E_1$ with the set of $\Gamma'$-orbits of darts of $\mathcal T$ whose chosen representative has origin of colour $0$, such that $w(e_1)$ is the cardinality of the stabiliser in $\Gamma'$ of that representative dart; let $D_2$, $eE_2$, and the corresponding width hypothesis be the analogous data for the $G$-orbits of darts. Let $\mu : D_1 \to D_2$ be a `FiniteHom`: maps $\mathrm{mapV}$, $\mathrm{mapE}$ compatible with $a$ and $b$, local degrees $\deg : E_1 \to \mathbb Z_{>0}$, vertex degrees and a total degree, satisfying $w_2(\mathrm{mapE}\,e) = \deg(e)\, w_1(e)$, the two harmonicity conditions that for each $v \in V_1$ and each edge $e'$ of $D_2$ with $a(e') = \mathrm{mapV}(v)$ (respectively $b(e') = \mathrm{mapV}(v)$) the degrees of the edges at $v$ over $e'$ sum to $\deg_V(v)$, and the condition that the vertex degrees in each fibre of $\mathrm{mapV}$ sum to the total degree. Assume moreover that $\mu$ is compatible with the orbit descriptions: for every $e_1$, the edge $eE_2(\mathrm{mapE}\,e_1)$ is the $G$-orbit of the chosen dart representative of $eE_1(e_1)$. Fix a base vertex $v_0$, and additive homomorphisms $\Phi_1$ from $\mathrm{Abelianization}\,\Gamma'$ to the cycle group $\mathrm{ribbonKernel}\,D_1$ (the intersection of the kernels of the push-forwards along $a$ and $b$) and $\Phi_2$ from $\mathrm{Abelianization}\,G$ to $\mathrm{ribbonKernel}\,D_2$, such that the value of $\Phi_i$ on the class of a group element $g$ is the cycle $\mathrm{pathCycle}$ of $g$, obtained by summing the dart-indices relative to each orbit along a chosen path from $v_0$ to $g \cdot v_0$. Then for every $\gamma \in G$ the pull-back $\mu^{*}$, given by $(\mu^{*}y)(e_1) = \deg(e_1)\, y(\mathrm{mapE}\,e_1)$, satisfies $\mu^{*}(\Phi_2(\bar\gamma)) = \Phi_1(\mathrm{Ver}(\gamma))$, where $\mathrm{Ver} : G \to \mathrm{Abelianization}\,\Gamma'$ is the transfer of the abelianisation map of $\Gamma'$.
--
--   This is the compatibility of the Bass–Serre cycle maps attached to the weighted quotient graphs $\Gamma' \backslash \mathcal T$ and $G \backslash \mathcal T$ with the transfer (Verlagerung) homomorphism, in the form needed when the tree lattice has torsion, so that edge widths are stabiliser orders and the quotient map has local degrees given by stabiliser indices. It is used in the Mumford-curve period computations, where pull-back along a covering of totally degenerate curves must be matched with the transfer on the uniformising groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer.lean

import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_AlgebraicCurve_TotallyDegenerateCovering_Hom
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Transfer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.finiteHom_pullback_apply_eq_apply_transfer_of_forall_apply_eq_pathCycle_of_card_stabilizer
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hT : 𝒯.IsTree) (hfin : ∀ w : W, Finite (stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    (Γ' : Subgroup G) [Γ'.FiniteIndex] [GraphAction ↥Γ' 𝒯]
    [DecidableEq (QuotEdge G 𝒯)] [DecidableEq (QuotEdge ↥Γ' 𝒯)]
    {E₁ V₁ : Type} [Fintype E₁] [Fintype V₁] [DecidableEq V₁] (D₁ : DegeneracyData E₁ V₁)
    (eE₁ : E₁ ≃ {e : QuotEdge ↥Γ' 𝒯 // τ e.out.fst = 0})
    (hw₁ : ∀ e₁ : E₁, (D₁.w e₁ : ℕ) = Nat.card (stabilizer ↥Γ' (((eE₁ e₁).1).out : 𝒯.Dart)))
    {E₂ V₂ : Type} [Fintype E₂] [DecidableEq E₂] [DecidableEq V₂] (D₂ : DegeneracyData E₂ V₂)
    (eE₂ : E₂ ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (hw₂ : ∀ e₂ : E₂, (D₂.w e₂ : ℕ) = Nat.card (stabilizer G (((eE₂ e₂).1).out : 𝒯.Dart)))
    (μ : D₁.FiniteHom D₂)
    (hμE : ∀ e₁ : E₁, ((eE₂ (μ.mapE e₁)).1 : QuotEdge G 𝒯) = Quotient.mk (orbitRel G 𝒯.Dart) ((eE₁ e₁).1).out)
    (v₀ : W)
    (Φ₁ : Additive (Abelianization ↥Γ') →+ ↥(ribbonKernel D₁))
    (hΦ₁ : ∀ g : ↥Γ', (Φ₁ (Additive.ofMul (Abelianization.of g)) : E₁ → ℤ) = pathCycle 𝒯 (fun e => (eE₁ e).1) v₀ g)
    (Φ₂ : Additive (Abelianization G) →+ ↥(ribbonKernel D₂))
    (hΦ₂ : ∀ g : G, (Φ₂ (Additive.ofMul (Abelianization.of g)) : E₂ → ℤ) = pathCycle 𝒯 (fun e => (eE₂ e).1) v₀ g)
    (γ : G) :
    μ.pullback (Φ₂ (Additive.ofMul (Abelianization.of γ))) =
      Φ₁ (Additive.ofMul (MonoidHom.transfer (Abelianization.of : ↥Γ' →* Abelianization ↥Γ') γ)) := by sorry
