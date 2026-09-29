-- Prove2me | Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_length_piece_quotient_eq_of_isHomogeneousVBasis_of_comm_verschiebung
-- name    : CerednikDrinfeld.GradedCartierModuleData.length_piece_quotient_eq_of_isHomogeneousVBasis_of_comm_verschiebung
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/93845810-a2f6-5054-9d2b-8cc41b89e4fa
-- title:
--   Equal colengths in both graded pieces of a V-commuting injection
-- statement:
--   Fix a prime $p$ and a perfect field $K$ of characteristic $p$, together with a ring homomorphism $j$ from $W(\mathbb{F}_{p^2})$ to $K$, and let $D$, $D'$ be two instances of `GradedCartierModuleData` for $(p,K,j)$: each consists of a module $M$ over the Witt vectors $W(K)$ carrying additive endomorphisms $F$ and $V$ and a $W(K)$-linear $\varpi$ satisfying the usual Cartier-type identities ($F$ is $\sigma$-semilinear, $w\cdot Vx = V(\sigma(w)x)$, $V(w\,Fx) = V(w)\,x$, $FV = p$, $\varpi$ commuting with $F$ and $V$ and $\varpi^2 = p$), together with a pair of submodules $M_0, M_1$ indexed by `Fin 2` forming complements of one another and permuted by $F$, $V$ and $\varpi$ according to $i \mapsto i+1$. Assume $\gamma : \mathrm{Fin}\,2 \to M$ is a homogeneous $V$-basis of $D$, that is, $\gamma_i \in M_i$ and every $x \in M$ is uniquely of the form $\sum_i \tau(c_i)\,\gamma_i + V y$ with $c \in K^{\mathrm{Fin}\,2}$ (Teichmüller lifts $\tau$) and $y \in M$, and likewise $\gamma'$ for $D'$. Let $f : M \to M'$ be $W(K)$-linear, injective, with $f(Vx) = V'(f x)$ for all $x$, and with $f(M_i) \subseteq M'_i$ for $i = 0,1$. Then the $W(K)$-lengths (in $\mathbb{N}_\infty$) of the quotient of $M'_0$ by the preimage in $M'_0$ of the submodule $f(M_0)$ and of the quotient of $M'_1$ by the preimage in $M'_1$ of $f(M_1)$ are equal.
--
--   This is the colength-balance statement for graded Cartier modules: a graded, $V$-equivariant injection has the same colength in degree $0$ as in degree $1$. It is the abstract core of the length computation for isogenies of special formal $\mathcal{O}_D$-modules used in the Čerednik–Drinfeld uniformisation, and is applied in [`CerednikDrinfeld.FormalODModule.length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial`](thm.html#CerednikDrinfeld.FormalODModule.length_gradedSubmodule_quotient_range_mapLinear_eq_of_isIsogenyOfHeight_two_mul_of_isSpecial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_GradedCartierModuleData_length_piece_quotient_eq_of_isHomogeneousVBasis_of_comm_verschiebung.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.GradedCartierModuleData.length_piece_quotient_eq_of_isHomogeneousVBasis_of_comm_verschiebung
    (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [CharP K p] [PerfectRing K p] {j : Zp2 p →+* K}
    (D D' : GradedCartierModuleData p K j)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (γ' : Fin 2 → D'.M) (hγ' : D'.IsHomogeneousVBasis γ')
    (f : D.M →ₗ[WittVector p K] D'.M) (hf : Function.Injective f)
    (hfV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hfdeg : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) :
    Module.length (WittVector p K)
        (↥(D'.piece 0) ⧸ Submodule.comap (D'.piece 0).subtype (Submodule.map f (D.piece 0))) =
      Module.length (WittVector p K)
        (↥(D'.piece 1) ⧸ Submodule.comap (D'.piece 1).subtype (Submodule.map f (D.piece 1))) := by sorry
