-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/27f6d134-90b2-5377-94ac-d62b2673dca3
-- title:
--   Gluing the modules of Drinfeld data along basic opens
-- statement:
--   Let $\mathcal O$ be a commutative ring, $K$ a field with an $\mathcal O$-algebra structure, $\pi \in \mathcal O$, and $B$ a commutative $\mathcal O$-algebra. Let $f : \mathrm{Fin}\,k \to B$ be such that the $f_i$ generate the unit ideal of $B$. For each $i$ let $Q_i$ be a Drinfeld datum for $(\pi, K)$ over $\mathrm{Localization.Away}\,(f_i)$: families of full $\mathcal O$-lattices $N_0(x) \le N_1(x)$ in $K^2$ indexed by the spectrum, with $\pi N_1(x) \subseteq N_0(x)$ and open membership loci, together with invertible modules $T_0, T_1$ over that ring, maps $\Pi_0 : T_0 \to T_1$, $\Pi_1 : T_1 \to T_0$ whose composites in either order are multiplication by $\pi$, and stalkwise identifications $u_0, u_1$ of the base-changed lattices with the stalks of $T_0, T_1$ compatible with the inclusion and with multiplication by $\pi$. For each pair $(i,j)$ let $C_{ij}$ be a commutative ring that is an $\mathcal O$-algebra and a localisation of $B$ away from $f_i f_j$, carrying compatible algebra structures over $\mathrm{Localization.Away}\,(f_i)$ and $\mathrm{Localization.Away}\,(f_j)$, let $Q_{ij}$ be a Drinfeld datum over $C_{ij}$, and let $W^{\mathrm l}_{ij}$, $W^{\mathrm r}_{ij}$ be data exhibiting $Q_{ij}$ as a base change of $Q_i$ and of $Q_j$ along the respective structural maps: equalities of the lattices at points lying under, and semilinear maps $\tau_0, \tau_1$ with $C_{ij}$-spanning images, commuting with the $\Pi$'s and compatible with the $u$'s. Assume further that each $(Q_i).T_0$ and $(Q_i).T_1$ carries a $B$-module structure compatible with its module structure over $\mathrm{Localization.Away}\,(f_i)$. Then there exist invertible $B$-modules $T_0, T_1$, $B$-linear maps $\Pi_0 : T_0 \to T_1$ and $\Pi_1 : T_1 \to T_0$ with $\Pi_1 \Pi_0 = \pi$ and $\Pi_0 \Pi_1 = \pi$ (scalar multiplication by the image of $\pi$ in $B$), and $B$-linear maps $p_0^i : T_0 \to (Q_i).T_0$, $p_1^i : T_1 \to (Q_i).T_1$ which exhibit $(Q_i).T_0$, $(Q_i).T_1$ as the localisations of $T_0$, $T_1$ at the powers of $f_i$, such that $p_1^i \circ \Pi_0 = (Q_i).\Pi_0 \circ p_0^i$, $p_0^i \circ \Pi_1 = (Q_i).\Pi_1 \circ p_1^i$, and for all $i, j$ the two comparison maps agree: $(W^{\mathrm l}_{ij}).\tau_0 \circ p_0^i = (W^{\mathrm r}_{ij}).\tau_0 \circ p_0^j$ and likewise in degree $1$.
--
--   This is the module half of the assertion that Drinfeld's functor of quadruples is a Zariski sheaf: given Drinfeld data on a finite cover of $\mathrm{Spec}\,B$ by basic opens, with prescribed identifications of their base changes on the pairwise overlaps, the invertible modules $T_0, T_1$ together with $\Pi_0, \Pi_1$ descend to $B$. It is used in the construction of a Drinfeld datum over $B$ itself, via [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_forall_isBaseChangeAlong_away_of_overlap`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_forall_isBaseChangeAlong_away_of_overlap); the lattice families and the stalk identifications are not part of the conclusion here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_gluedModules_of_baseChangeAlong_overlap.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_gluedModules_of_baseChangeAlong_overlap
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {k : ℕ} (f : Fin k → B) (hf : Ideal.span (Set.range f) = ⊤)
    (Q : ∀ i : Fin k, DrinfeldDatum (K := K) π (Localization.Away (f i)))
    (C : Fin k → Fin k → Type) [∀ i j, CommRing (C i j)] [∀ i j, Algebra B (C i j)] [∀ i j, Algebra 𝒪 (C i j)]
    [∀ i j, IsScalarTower 𝒪 B (C i j)] [∀ i j, IsLocalization.Away (f i * f j) (C i j)]
    [∀ i j, Algebra (Localization.Away (f i)) (C i j)] [∀ i j, Algebra (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower B (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower B (Localization.Away (f j)) (C i j)]
    [∀ i j, IsScalarTower 𝒪 (Localization.Away (f i)) (C i j)] [∀ i j, IsScalarTower 𝒪 (Localization.Away (f j)) (C i j)]
    (Q₂ : ∀ i j : Fin k, DrinfeldDatum (K := K) π (C i j))
    (Wl : ∀ i j : Fin k, (Q i).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f i)) (C i j)) (Q₂ i j))
    (Wr : ∀ i j : Fin k, (Q j).BaseChangeAlong (IsScalarTower.toAlgHom 𝒪 (Localization.Away (f j)) (C i j)) (Q₂ i j))
    [∀ i, Module B (Q i).T₀] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₀]
    [∀ i, Module B (Q i).T₁] [∀ i, IsScalarTower B (Localization.Away (f i)) (Q i).T₁] :
    ∃ (T₀ T₁ : Type) (_ : AddCommGroup T₀) (_ : AddCommGroup T₁) (_ : Module B T₀) (_ : Module B T₁)
      (_ : Module.Invertible B T₀) (_ : Module.Invertible B T₁)
      (Pi₀ : T₀ →ₗ[B] T₁) (Pi₁ : T₁ →ₗ[B] T₀) (p₀ : ∀ i, T₀ →ₗ[B] (Q i).T₀) (p₁ : ∀ i, T₁ →ₗ[B] (Q i).T₁),
      (∀ t, Pi₁ (Pi₀ t) = algebraMap 𝒪 B π • t) ∧ (∀ t, Pi₀ (Pi₁ t) = algebraMap 𝒪 B π • t) ∧
      (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₀ i)) ∧
      (∀ i, IsLocalizedModule (Submonoid.powers (f i)) (p₁ i)) ∧
      (∀ i t, p₁ i (Pi₀ t) = (Q i).Pi₀ (p₀ i t)) ∧ (∀ i t, p₀ i (Pi₁ t) = (Q i).Pi₁ (p₁ i t)) ∧
      (∀ i j t, (Wl i j).τ₀ (p₀ i t) = (Wr i j).τ₀ (p₀ j t)) ∧
      (∀ i j t, (Wl i j).τ₁ (p₁ i t) = (Wr i j).τ₁ (p₁ j t)) := by sorry
