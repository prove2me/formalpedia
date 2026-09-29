-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_standard_existsUnique_eq_add_mul
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_standard_existsUnique_eq_add_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/0f6abaae-1e7d-5cb1-b2cd-45cf0b879338
-- title:
--   mathcal O_D-linear endomorphisms of Drinfeld's standard special module
-- statement:
--   Let $p$ be a prime, let $k$ be a field of characteristic $p$, and let $j\colon \mathbb Z_{p^2}=W(\mathbb F_{p^2})\to k$ be a ring homomorphism. Consider the standard special formal $\mathcal O_D$-module `SpecialFormalODModule.standard j` over $k$: its underlying `FormalODModule` consists of a two-dimensional commutative formal group law $F$ together with substitution series `act a` ($a\in\mathbb Z_{p^2}$) and `varpi`, all endomorphisms of $F$, satisfying $\mathrm{act}(1)=\mathrm{id}$, multiplicativity and additivity of $a\mapsto \mathrm{act}(a)$, $\mathrm{varpi}\circ\mathrm{varpi}=\mathrm{act}(p)$ and $\mathrm{varpi}\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\mathrm{varpi}$ for the Witt vector Frobenius $\sigma$, and which in addition is special relative to $j$ and of height $4$. Write $C$ for the centraliser, inside the endomorphism ring of $F$, of the set consisting of all `actEnd` endomorphisms $\mathrm{act}(a)$ together with the single element `varpiEnd`. The assertion is that there exist a ring homomorphism $A\colon\mathbb Z_{p^2}\to C$ and an element $\Psi\in C$ such that, in terms of the matrix units $\mathrm{cell}_{i i'}$ which build an endomorphism of $F$ from an endomorphism $e$ of $\bar\Sigma$ (the reduction along $j$ of the one-dimensional Lubin–Tate law) by composing the inclusion of the $i$-th factor, $e$ and the projection onto the $i'$-th factor: $A(a)=\mathrm{cell}_{00}(\rho(a))+\mathrm{cell}_{11}(\rho(a))$ for all $a$, where $\rho\colon\mathbb Z_{p^2}\to\operatorname{End}(\bar\Sigma)$ is the reduced Lubin–Tate action; $\Psi=\mathrm{cell}_{01}(\rho(p)\varphi)+\mathrm{cell}_{10}(\varphi)$, where $\varphi$ is the endomorphism $T\mapsto T^{p}$ of $\bar\Sigma$; $\Psi^2=A(p^2)$; $\Psi A(a)=A(\sigma a)\Psi$ for all $a$; and every element of $C$ is uniquely of the form $A(a)+A(c)\Psi$ with $(a,c)\in\mathbb Z_{p^2}\times\mathbb Z_{p^2}$.
--
--   This is Drinfeld's computation of the ring of $\mathcal O_D$-linear endomorphisms of the standard special formal $\mathcal O_D$-module of height four, identifying it with the order $\mathbb Z_{p^2}\oplus\mathbb Z_{p^2}\Psi$ in the cyclic algebra $(\mathbb Q_{p^2}/\mathbb Q_p,\sigma,p^2)$. It is used by [`CerednikDrinfeld.SpecialFormalODModule.exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective`](thm.html#CerednikDrinfeld.SpecialFormalODModule.exists_forall_nsmul_eq_zero_imp_and_exists_ringHom_centralizer_injective) in the analysis of the quaternionic action underlying the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_ringHom_centralizer_standard_existsUnique_eq_add_mul.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_LubinTateModule
import Definitions.Def_CerednikDrinfeld_StandardFormalODModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld in

theorem CerednikDrinfeld.SpecialFormalODModule.exists_ringHom_centralizer_standard_existsUnique_eq_add_mul
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] (j : Zp2 p →+* k) :
    ∃ (A : Zp2 p →+*
          Subring.centralizer
            (Set.range (SpecialFormalODModule.standard j).toFormalODModule.actEnd ∪
              {(SpecialFormalODModule.standard j).toFormalODModule.varpiEnd}))
      (Ψ : Subring.centralizer
            (Set.range (SpecialFormalODModule.standard j).toFormalODModule.actEnd ∪
              {(SpecialFormalODModule.standard j).toFormalODModule.varpiEnd})),
      (∀ a, (A a : MvFormalGroup.End (SpecialFormalODModule.standard j).F) =
          Standard.cell j 0 0 (LubinTate.rho j a) + Standard.cell j 1 1 (LubinTate.rho j a)) ∧
      (Ψ : MvFormalGroup.End (SpecialFormalODModule.standard j).F) =
          Standard.cell j 0 1 (LubinTate.rho j (p : Zp2 p) * LubinTate.phi j) +
            Standard.cell j 1 0 (LubinTate.phi j) ∧
      Ψ * Ψ = A ((p : Zp2 p) ^ 2) ∧
      (∀ a, Ψ * A a = A (WittVector.frobenius a) * Ψ) ∧
      ∀ e, ∃! ac : Zp2 p × Zp2 p, e = A ac.1 + A ac.2 * Ψ := by sorry
