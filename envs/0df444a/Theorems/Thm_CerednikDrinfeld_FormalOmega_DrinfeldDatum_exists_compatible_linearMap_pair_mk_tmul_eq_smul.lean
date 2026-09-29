-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_compatible_linearMap_pair_mk_tmul_eq_smul
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_compatible_linearMap_pair_mk_tmul_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/b18f3093-4a14-57d2-bd04-c106b8d2b225
-- title:
--   Drinfeld datum near a point: Pi-compatible pair of linear maps
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring which is a domain, $K$ a field that is a fraction field of $\mathcal{O}$, $\pi \in \mathcal{O}$, and $B$ a commutative $\mathcal{O}$-algebra. Let $Q$ be a Drinfeld datum for $\pi$ over $B$: it consists of families $N_0, N_1$ assigning to each $y \in \operatorname{Spec} B$ finitely generated $\mathcal{O}$-submodules of $K^2$ spanning $K^2$ over $K$, with $N_0(y) \subseteq N_1(y)$ and $\pi N_1(y) \subseteq N_0(y)$, the membership loci of each vector being open; invertible $B$-modules $T_0, T_1$ with $B$-linear maps $\Pi_0 : T_0 \to T_1$, $\Pi_1 : T_1 \to T_0$ whose two composites are multiplication by the image of $\pi$; and for each $y$ a $B_y$-linear map $u_i(y) : B_y \otimes_{\mathcal{O}} N_i(y) \to (T_i)_y$ compatible with the inclusion, with multiplication by $\pi$, and with $\Pi_0, \Pi_1$. Fix $x \in \operatorname{Spec} B$ and $r_0 \in B$ with $r_0 \notin x$, and assume $N_0(x) \subseteq N_0(y)$ and $N_1(x) \subseteq N_1(y)$ for every $y$ with $r_0 \notin y$. Then there is $r \in B$ with $r \notin x$ and $r_0 \mid r$, together with $B$-linear maps $A_0 : B \otimes_{\mathcal{O}} N_0(x) \to T_0$ and $A_1 : B \otimes_{\mathcal{O}} N_1(x) \to T_1$ such that: $A_1$ composed after the base change of the inclusion $N_0(x) \subseteq N_1(x)$ equals $\Pi_0 \circ A_0$; $A_0$ composed after the base change of multiplication by $\pi$ from $N_1(x)$ to $N_0(x)$ equals $\Pi_1 \circ A_1$; for every $y$ with $r_0 \notin y$ and $r \notin y$ and every $v \in N_0(x)$, the image of $A_0(1 \otimes v)$ in the localisation of $T_0$ at $y$ equals $r \cdot u_0(y)(1 \otimes v)$, with $v$ regarded in $N_0(y)$, and likewise for index $1$; and for every $t \in T_0$ (respectively $t \in T_1$) there are an element $w$ of the source and $n \in \mathbb{N}$ with $A_0 w = r^n t$ (respectively $A_1 w = r^n t$).
--
--   This is the local spreading-out step for Drinfeld data in the Čerednik–Drinfeld uniformisation, corresponding to the first display of Boutot–Carayol I (5.5): on the locus where the two fixed lattices at $x$ are contained in the lattice families, the composite stalk maps are, near $x$, induced by a single $\Pi$-compatible pair of homomorphisms of $B$-modules, these becoming surjective after inverting $r$. It is obtained from the spreading lemma [`LocalizedModule.exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk`](thm.html#LocalizedModule.exists_linearMap_mk_tmul_eq_smul_of_forall_exists_eq_mk) applied to the two families of stalk maps, and is used in [`CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_deligneDatum_away_forall_map`](thm.html#CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_deligneDatum_away_forall_map).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_exists_compatible_linearMap_pair_mk_tmul_eq_smul.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.exists_compatible_linearMap_pair_mk_tmul_eq_smul
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
    [IsFractionRing 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Q : DrinfeldDatum (K := K) π B) (x : PrimeSpectrum B) (r₀ : B) (hr₀ : r₀ ∉ x.asIdeal)
    (h₀ : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal → Q.N₀ x ≤ Q.N₀ y)
    (h₁ : ∀ y : PrimeSpectrum B, r₀ ∉ y.asIdeal → Q.N₁ x ≤ Q.N₁ y) :
    ∃ r : B, r ∉ x.asIdeal ∧ r₀ ∣ r ∧
      ∃ (A₀ : latticeBaseChange 𝒪 K B (Q.L₀ x) →ₗ[B] Q.T₀) (A₁ : latticeBaseChange 𝒪 K B (Q.L₁ x) →ₗ[B] Q.T₁),
        (∀ w, A₁ (inclBaseChange B (M' := Q.L₀ x) (M := Q.L₁ x) (Q.le x) w) = Q.Pi₀ (A₀ w)) ∧
        (∀ w, A₀ (((smulInto π (Q.smul_le x)).baseChange B :
            latticeBaseChange 𝒪 K B (Q.L₁ x) →ₗ[B] latticeBaseChange 𝒪 K B (Q.L₀ x)) w) = Q.Pi₁ (A₁ w)) ∧
        (∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal), r ∉ y.asIdeal → ∀ v : ↥(Q.N₀ x),
          LocalizedModule.mk (A₀ ((1 : B) ⊗ₜ[𝒪] v)) 1 =
            algebraMap B (locRing B y) r • Q.u₀ y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, h₀ y hy v.2⟩ : ↥(Q.N₀ y)))) ∧
        (∀ (y : PrimeSpectrum B) (hy : r₀ ∉ y.asIdeal), r ∉ y.asIdeal → ∀ v : ↥(Q.N₁ x),
          LocalizedModule.mk (A₁ ((1 : B) ⊗ₜ[𝒪] v)) 1 =
            algebraMap B (locRing B y) r • Q.u₁ y ((1 : locRing B y) ⊗ₜ[𝒪] (⟨v, h₁ y hy v.2⟩ : ↥(Q.N₁ y)))) ∧
        (∀ t : Q.T₀, ∃ (w : latticeBaseChange 𝒪 K B (Q.L₀ x)) (n : ℕ), A₀ w = r ^ n • t) ∧
        (∀ t : Q.T₁, ∃ (w : latticeBaseChange 𝒪 K B (Q.L₁ x)) (n : ℕ), A₁ w = r ^ n • t) := by sorry
