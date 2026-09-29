-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq
-- name    : CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/3bed5387-3749-5919-9411-6d1a4279b6e3
-- title:
--   Lifting a formal mathcal O_D-module by lifting its structure constants
-- statement:
--   Let $p$ be a prime, let $B$ and $B'$ be commutative rings in a common universe, let $j' : \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to B'$ and $\varphi : B' \to B$ be ring homomorphisms, and assume $B$ is Hausdorff for the ideal $(p)$. Let $X$ be a formal $\mathcal O_D$-module over $B$, that is, a commutative $2$-dimensional formal group law $X.F$ over $B$ together with an action of $W(\mathbb{F}_{p^2})$ by endomorphisms of the law and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma(a)]\circ\varpi$ for the Frobenius $\sigma$ of $W(\mathbb{F}_{p^2})$. Let $\gamma_0,\gamma_1$ be elements of the Cartier module of $X.F$ forming a homogeneous $V$-basis for $\varphi\circ j'$: each $\gamma_i$ lies in the $i$-th graded piece, i.e. the Teichmüller lift of every $c \in \mathbb{F}_{p^2}$ acts on $\gamma_i$ as the homothety by $(\varphi\circ j')(\tau(c))^{p^i}$, and the matrix of tangent vectors $(\mathrm{tangent}(\gamma_i)_k)_{i,k}$ has unit determinant. Let $a : \mathbb{N} \to \mathrm{Fin}\,2 \to B$ be structure constants for $\gamma$: for every $i$ and every $N$, $\varpi\cdot\gamma_i = \sum_{m<N} V^m\big(a_{m,i}\,\gamma_{\pi(m,i)}\big) + V^N h$ for some $h$ in the Cartier module, where $\pi(m,i) = (m+i+1) \bmod 2$ and $V$ is the integral Verschiebung. Finally let $a' : \mathbb{N} \to \mathrm{Fin}\,2 \to B'$ satisfy $\varphi(a'_{m,i}) = a_{m,i}$ for all $m,i$ and $a'_{0,0}a'_{0,1} = p$ in $B'$. Then there exist a formal $\mathcal O_D$-module $X'$ over $B'$ and $\gamma'_0,\gamma'_1$ in the Cartier module of $X'.F$ which form a homogeneous $V$-basis for $j'$ with structure constants $a'$, together with a homomorphism $u$ from the base change $X'\otimes_{\varphi}B$ to $X$ that is an isomorphism (it admits a two-sided inverse) and satisfies $\mathrm{CartierModule.map}(u)\big(\mathrm{baseChange}_\varphi(\gamma'_i)\big) = \gamma_i$ for $i = 0,1$.
--
--   This is the Cartier-theoretic lifting step for Drinfeld's moduli problem of special formal $\mathcal O_D$-modules: a formal $\mathcal O_D$-module over $B$ with a homogeneous $V$-basis lifts along $\varphi : B' \to B$, compatibly with the basis, as soon as its structure constants lift to elements of $B'$ satisfying the single relation $a'_{0,0}a'_{0,1} = p$. It is used in the proofs that the relevant deformation functors are prorepresentable by explicit power series rings, via surjections onto the deformation rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_hasStructureConstants_and_isIso_map_of_forall_apply_eq
    (p : ℕ) [Fact p.Prime] {B B' : Type u} [CommRing B] [CommRing B']
    (j' : CerednikDrinfeld.Zp2 p →+* B') (φ : B' →+* B)
    (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
    (X : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis (φ.comp j') γ)
    (a : ℕ → Fin 2 → B) (ha : X.HasStructureConstants γ a)
    (a' : ℕ → Fin 2 → B') (ha' : ∀ m i, φ (a' m i) = a m i) (h01 : a' 0 0 * a' 0 1 = (p : B')) :
    ∃ (X' : CerednikDrinfeld.FormalODModule p B') (γ' : Fin 2 → MvFormalGroup.CartierModule p X'.F),
      X'.IsHomogeneousVBasis j' γ' ∧ X'.HasStructureConstants γ' a' ∧
        ∃ u : (X'.map φ).Hom X, u.IsIso ∧ ∀ i : Fin 2,
          MvFormalGroup.CartierModule.map u.toLawHom
            (MvFormalGroup.CartierModule.baseChange φ (γ' i)) = γ i := by sorry
