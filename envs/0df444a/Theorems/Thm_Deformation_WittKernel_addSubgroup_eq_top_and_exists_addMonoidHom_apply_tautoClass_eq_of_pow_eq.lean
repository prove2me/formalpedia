-- Prove2me | Theorems.Thm_Deformation_WittKernel_addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
-- name    : Deformation.WittKernel.addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/e6e1dc41-c3f7-56a5-9ed2-2e98e8a7a539
-- title:
--   Tautological classes generate and present the Witt-kernel Dieudonné module
-- statement:
--   Let $p$ be a prime, let $n,a,b$ be natural numbers with $a<b$, let $J$ be a finite type, and let $D$ be an additive commutative group carrying a Dieudonné datum `MD` with parameter $(p:\mathbb Z)$, that is, a pair of endomorphisms $F=$ `MD.F` and $V=$ `MD.V` of $D$ with $F\circ V=V\circ F=p\cdot\mathrm{id}$; assume $V^n=0$ and $F^b=F^a$, and let $d\colon J\to D$ be any family of elements. Write $C=$ [`Deformation.WittKernel.Coord (ZMod p) p n a b J`](def/Dieudonne_WittKernelHopf.html#L204) for the quotient of the polynomial algebra `MvPolynomial (J × Fin n) (ZMod p)` by the ideal spanned by the elements `relation` indexed by $J\times\mathrm{Fin}\,n$, and let $M=$ [`Deformation.DieudonneModule (ZMod p) p C`](def/Dieudonne_WittHomColimit.html#L234) be the colimit, over the truncation level, of the subgroups [`Deformation.wittHom (ZMod p) p m C`](def/Dieudonne_WittVectorHom.html#L246) of `TruncatedWittVector p m C` cut out by the primitivity condition for the comultiplication of $C$, with its induced Frobenius and Verschiebung operators and with the classes [`Deformation.WittKernel.tautoClass … j`](def/Dieudonne_WittKernelHopf.html#L308) coming from the $j$-th tautological truncated Witt vector of length $n$. The assertion is twofold: first, every subgroup $N\le M$ stable under Frobenius and under Verschiebung and containing all the tautological classes equals $\top$; second, there exists an additive map $\rho\colon M\to D$ with $\rho\circ\mathrm{Frob}=F\circ\rho$, $\rho\circ\mathrm{Versch}=V\circ\rho$, and $\rho$ sending the $j$-th tautological class to $d\,j$ for every $j$.
--
--   Taken together, the two clauses say that $M$ is free of rank $\#J$ on the tautological classes over $\mathbb Z[F,V]/(FV-p,V^n,F^b-F^a)$, the analogue for the finite kernel groups $W_n^J[F^b-F^a]$ of the classical computation of the Dieudonné module of the Witt group $W_n$. It is used by [`Deformation.DieudonneDatum.exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent`](thm.html#Deformation.DieudonneDatum.exists_hopfAlgebra_zmod_addEquiv_dieudonneModule_of_isNilpotent) to realise a given Dieudonné datum with nilpotent Verschiebung as the Dieudonné module of a finite commutative group scheme over $\mathbb F_p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_WittKernel_addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_WittGroupHopf
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Definitions.Def_Dieudonne_WittKernelHopf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe v w

theorem Deformation.WittKernel.addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
    (p : ℕ) [Fact p.Prime] (n a b : ℕ) (hab : a < b) (J : Type v) [Finite J]
    {D : Type w} [AddCommGroup D] (MD : Deformation.DieudonneDatum (p : ℤ) D)
    (hV : MD.V ^ n = 0) (hF : MD.F ^ b = MD.F ^ a) (d : J → D) :
    (∀ N : AddSubgroup (Deformation.DieudonneModule (ZMod p) p
        (Deformation.WittKernel.Coord (ZMod p) p n a b J)),
      (∀ z ∈ N, Deformation.DieudonneModule.frobenius (ZMod p) p _ z ∈ N) →
      (∀ z ∈ N, Deformation.DieudonneModule.verschiebung (ZMod p) p _ z ∈ N) →
      (∀ j, Deformation.WittKernel.tautoClass (ZMod p) p n a b J j ∈ N) → N = ⊤) ∧
    ∃ ρ : Deformation.DieudonneModule (ZMod p) p (Deformation.WittKernel.Coord (ZMod p) p n a b J) →+ D,
      (∀ z, ρ (Deformation.DieudonneModule.frobenius (ZMod p) p _ z) = MD.F (ρ z)) ∧
      (∀ z, ρ (Deformation.DieudonneModule.verschiebung (ZMod p) p _ z) = MD.V (ρ z)) ∧
      ∀ j, ρ (Deformation.WittKernel.tautoClass (ZMod p) p n a b J j) = d j := by sorry
