-- Prove2me | Theorems.Thm_Deformation_HondaSystem_range_sup_eq_top_of_isArtinian_of_isNoetherian
-- name    : Deformation.HondaSystem.range_sup_eq_top_of_isArtinian_of_isNoetherian
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/cc7ce394-0790-5c08-879b-67f132170e46
-- title:
--   Length count: im F + L = D for finite-length Dieudonné data
-- statement:
--   Let $S$ be a commutative ring and $D$ an $S$-module that is both Artinian and Noetherian, i.e. of finite length. Let $\sigma,\tau\colon S \to S$ be surjective ring endomorphisms, let $F\colon D \to D$ be $\sigma$-semilinear and $V\colon D \to D$ be $\tau$-semilinear, and let $\ell \in S$ satisfy $F(V(x)) = \ell \cdot x$ for all $x \in D$ (only this one of the two Dieudonné relations is assumed). Let $L \subseteq D$ be an $S$-submodule such that: (i) every $x \in L$ lying in the image of $F$ is of the form $\ell \cdot y$ for some $y \in L$; (ii) $V$ is injective on $L$, i.e. $x \in L$ and $V(x)=0$ force $x=0$; (iii) $\ker F \subseteq \operatorname{im} V$; and (iv) every $x \in D$ annihilated by $\ell$ decomposes as $x = y + z$ with $y \in L$ and $V(z) = 0$. The conclusion is that $\operatorname{im} F \sqcup L = \top$, i.e. $D = F(D) + L$.
--
--   This is the module-theoretic length computation with which Fontaine's theorem on Honda systems is concluded: hypotheses (i) and (ii) are the conditions `sh1_le` and `sh3` in the project's `HondaSystem` structure, and the conclusion is exactly its condition `sh2'`. It is used in [`Deformation.DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge`](thm.html#Deformation.DieudonneModule.exists_hondaSystem_L_eq_fontaineHodge) to verify that the Dieudonné module of the special fibre of a finite flat group scheme, together with Fontaine's submodule, forms a Honda system.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_HondaSystem_range_sup_eq_top_of_isArtinian_of_isNoetherian.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.HondaSystem.range_sup_eq_top_of_isArtinian_of_isNoetherian
    {S : Type u} [CommRing S] {D : Type v} [AddCommGroup D] [Module S D]
    [IsArtinian S D] [IsNoetherian S D]
    {σ τ : S →+* S} [RingHomSurjective σ] [RingHomSurjective τ]
    (F : D →ₛₗ[σ] D) (V : D →ₛₗ[τ] D) (ℓ : S) (hFV : ∀ x, F (V x) = ℓ • x)
    (L : Submodule S D)
    (sh1 : ∀ x ∈ L, x ∈ LinearMap.range F → ∃ y ∈ L, x = ℓ • y)
    (sh3 : ∀ x ∈ L, V x = 0 → x = 0)
    (hkerF : LinearMap.ker F ≤ LinearMap.range V)
    (htors : ∀ x : D, ℓ • x = 0 → ∃ y ∈ L, ∃ z : D, V z = 0 ∧ y + z = x) :
    LinearMap.range F ⊔ L = ⊤ := by sorry
