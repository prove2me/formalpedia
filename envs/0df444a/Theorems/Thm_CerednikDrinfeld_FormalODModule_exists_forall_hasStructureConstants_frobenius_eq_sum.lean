-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_hasStructureConstants_frobenius_eq_sum
-- name    : CerednikDrinfeld.FormalODModule.exists_forall_hasStructureConstants_frobenius_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/87b551a3-a9db-5602-9739-194fa9337f1f
-- title:
--   Universal structure constants for Frobenius in a homogeneous V-basis
-- statement:
--   Let $p$ be a prime and let $B$ be a commutative ring equipped with a $\mathbb Z_p$-algebra structure, let $j : W(\mathbb F_{p^2}) \to B$ be a ring homomorphism (the source being [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the Witt vectors of the field with $p^2$ elements), and let $a : \mathbb N \to \mathrm{Fin}\,2 \to B$ be a family of elements of $B$. The assertion is that there exists a family $c : \mathbb N \to \mathrm{Fin}\,2 \to \mathrm{Fin}\,2 \to B$, depending only on the data above and in particular independent of what follows, such that for every formal $\mathcal O_D$-module $X$ over $B$ — a two-dimensional commutative formal group law $X.F$ over $B$ together with an action of $W(\mathbb F_{p^2})$ by endomorphisms of the law and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [p]$ and $\varpi\circ a = \sigma(a)\circ\varpi$ — and every pair $\gamma = (\gamma_0,\gamma_1)$ of elements of the Cartier module $\mathrm{CartierModule}\,p\,X.F$ such that: (i) $\gamma$ is a homogeneous $V$-basis for $j$, i.e. each $\gamma_i$ lies in the $i$-th graded piece (for every $c \in \mathbb F_{p^2}$, the Teichmüller element $\tau(c)$ acts on $\gamma_i$ by the homothety $j(\tau(c))^{p^i}$) and the determinant of the tangent matrix $(\mathrm{tangent}(\gamma_i)_k)_{i,k}$ is a unit in $B$; and (ii) $\gamma$ has structure constants $a$, i.e. for all $i$ and all $N$ there is $h$ with $\varpi_*\gamma_i = \sum_{m<N} V^m(\langle a_{m,i}\rangle\gamma_{(m+i+1)\bmod 2}) + V^N h$; one has: for every $i \in \mathrm{Fin}\,2$ and every $N \in \mathbb N$ there exists $h$ in the Cartier module with $$F\gamma_i = \sum_{m<N} V^m\Bigl(\sum_{k\in \mathrm{Fin}\,2} \langle c_{m,i,k}\rangle \gamma_k\Bigr) + V^N h,$$ where $F$ is `frobenius`, $V$ is `verschiebungInt` and $\langle b\rangle$ is `homothety`.
--
--   This is the step, following Boutot–Carayol's treatment of the Čerednik–Drinfeld uniformisation, in which the expansion of $\varpi$ on a homogeneous $V$-basis determines the expansion of the Cartier-module Frobenius by formulas universal in the formal $\mathcal O_D$-module: the constants $c$ are extracted from $a$ alone. It is used in the proof that a formal $\mathcal O_D$-module with prescribed structure constants admits a bijective map to a model, [`CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants`](thm.html#CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_forall_hasStructureConstants_frobenius_eq_sum.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_forall_hasStructureConstants_frobenius_eq_sum
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [Algebra (PadicInt p) B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (a : ℕ → Fin 2 → B) :
    ∃ c : ℕ → Fin 2 → Fin 2 → B,
      ∀ (X : CerednikDrinfeld.FormalODModule p B) (γ : Fin 2 → MvFormalGroup.CartierModule p X.F),
        X.IsHomogeneousVBasis j γ → X.HasStructureConstants γ a →
        ∀ (i : Fin 2) (N : ℕ), ∃ h : MvFormalGroup.CartierModule p X.F,
          MvFormalGroup.CartierModule.frobenius (γ i) =
            (∑ m : Fin N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[(m : ℕ)]
              (∑ k : Fin 2, MvFormalGroup.CartierModule.homothety (c m i k) (γ k))) +
            (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := X.F)))^[N] h := by sorry
