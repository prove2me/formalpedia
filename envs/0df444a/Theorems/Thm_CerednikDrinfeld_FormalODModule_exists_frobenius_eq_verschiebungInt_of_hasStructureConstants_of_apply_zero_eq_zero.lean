-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_frobenius_eq_verschiebungInt_of_hasStructureConstants_of_apply_zero_eq_zero
-- name    : CerednikDrinfeld.FormalODModule.exists_frobenius_eq_verschiebungInt_of_hasStructureConstants_of_apply_zero_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/8cb0ba5c-4b40-5f32-a6ff-ee946dc4e500
-- title:
--   Frobenius lands in VM when a_{0,i_0}=0
-- statement:
--   Let $q$ be a prime and $k$ a field of characteristic $q$, and let $X_0$ be a term of `FormalODModule q k`: a two-dimensional formal group law $F$ over $k$ together with the commutativity of $F$, a multiplicative and additive action `act` of $\mathbb{Z}_q^2$ by endomorphism series of $F$ and a further endomorphism series `varpi` satisfying $\varpi\circ\varpi=\mathrm{act}(q)$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\mathrm{Frob}\,a)\circ\varpi$. Write $M=$ `CartierModule q X₀.F` for the associated Cartier module, with its additive endomorphisms `frobenius` and `verschiebungInt` obtained by precomposition with the Verschiebung, resp. Frobenius, families of the Witt addition law, and $\Pi$ for the action of the endomorphism `X₀.varpiEnd` attached to `varpi`. Assume `verschiebungInt` is injective on $M$. Let $\gamma:\mathrm{Fin}\,2\to M$ and $a:\mathbb{N}\to\mathrm{Fin}\,2\to k$ satisfy `X₀.HasStructureConstants γ a`, i.e. for every index $i$ and every $N$ there is $h\in M$ with $\Pi\gamma_i=\sum_{m<N}V^m\big([a_{m,i}]\,\gamma_{\pi(m,i)}\big)+V^N h$, where $V=$ `verschiebungInt`, $[c]$ denotes homothety by $c$ and $\pi(m,i)=(m+i+1)\bmod 2$. If $i_0$ is an index with $a_{0,i_0}=0$, then there exists $y\in M$ with $F\gamma_{i_0}=Vy$.
--
--   This is the statement that a vanishing order-zero structure constant at the slot $i_0$ forces $F\gamma_{i_0}$ to lie in the image of Verschiebung on the Cartier module of a formal $\mathcal{O}_D$-module, in the Čerednik–Drinfeld setting. It is used in the analysis of first-order deformations of structure constants, where it rules out the only possible $\varepsilon$-contribution into one slot.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_frobenius_eq_verschiebungInt_of_hasStructureConstants_of_apply_zero_eq_zero.lean

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

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule in

theorem CerednikDrinfeld.FormalODModule.exists_frobenius_eq_verschiebungInt_of_hasStructureConstants_of_apply_zero_eq_zero
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
    (X₀ : FormalODModule q k)
    (hV : Function.Injective (MvFormalGroup.CartierModule.verschiebungInt (p := q) (Φ := X₀.F)))
    (γ : Fin 2 → MvFormalGroup.CartierModule q X₀.F) (a : ℕ → Fin 2 → k) (ha : X₀.HasStructureConstants γ a)
    (i₀ : Fin 2) (h0 : a 0 i₀ = 0) :
    ∃ y : MvFormalGroup.CartierModule q X₀.F,
      MvFormalGroup.CartierModule.frobenius (γ i₀) = MvFormalGroup.CartierModule.verschiebungInt y := by sorry
