-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar
-- name    : CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/de2ef4f4-86b8-5601-99b6-41be05da7717
-- title:
--   Universal formal mathcal O_D-module with homogeneous V-basis
-- statement:
--   Let $p$ be a prime and let $U=\mathbb Z_{p^2}[X_{m,i}:(m,i)\in\mathbb N\times\{0,1\}]/(X_{0,0}X_{0,1}-p)$, formed as [`CerednikDrinfeld.CartierLift.LiftRing`](def/CerednikDrinfeld_CartierStructureConstants.html#L180) over $\mathbb Z_{p^2}=W(\mathbb F_{p^2})$ by quotienting the polynomial ring on the index set $\mathbb N\times \mathrm{Fin}\,2$ by the single relation attached to the pair of variables $(0,0)$, $(0,1)$. The assertion is that there exist a `FormalODModule` $X$ over $U$, that is a commutative two-dimensional formal group law $F$ over $U$ together with an additive, multiplicative action of $\mathbb Z_{p^2}$ by endomorphisms of $F$ and a further endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma(a)]\circ\varpi$ for the Witt Frobenius $\sigma$, and two elements $\gamma_0,\gamma_1$ of the Cartier module of $F$ at $p$, such that: (i) relative to the structure map $\mathbb Z_{p^2}\to U$, each $\gamma_i$ is homogeneous of degree $i$, i.e. $[\omega(c)]$ acts on $\gamma_i$ as the homothety by $\omega(c)^{p^{i}}$ for every $c\in\mathbb F_{p^2}$, where $\omega$ denotes Teichmüller lifts, and the $2\times2$ matrix of tangent coefficients of the $\gamma_i$ has invertible determinant; and (ii) the structure constants of $\gamma$ are the universal ones: for every $i$ and every $N$ there is an element $h$ of the Cartier module with $$\varpi_*\gamma_i=\sum_{m<N}V^m\bigl(\langle X_{m,i}\rangle\,\gamma_{(m+i+1)\bmod 2}\bigr)+V^N h,$$ $V$ being the integral Verschiebung and $X_{m,i}$ the class of the corresponding variable in $U$.
--
--   This is the universal case of the existence of a special graded Cartier module, hence of a special formal $\mathcal O_D$-module, with prescribed structure constants subject only to $a_{0,0}a_{0,1}=p$, as in Boutot–Carayol's account of the Čerednik–Drinfeld uniformisation. It is the instance from which the version over an arbitrary $\mathbb Z_{p^2}$-algebra with arbitrary constants satisfying $a_{0,0}a_{0,1}=p$ is obtained, namely [`CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq`](thm.html#CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_of_mul_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar
    (p : ℕ) [Fact p.Prime] :
    ∃ (X : CerednikDrinfeld.FormalODModule p
          (CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1)))
      (γ : Fin 2 → MvFormalGroup.CartierModule p X.F),
      X.IsHomogeneousVBasis
          (algebraMap (CerednikDrinfeld.Zp2 p)
            (CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1))) γ ∧
        X.HasStructureConstants γ
          (fun m i => CerednikDrinfeld.CartierLift.liftVar (p := p) (R := CerednikDrinfeld.Zp2 p)
            ((0, 0) : ℕ × Fin 2) (0, 1) (m, i)) := by sorry
