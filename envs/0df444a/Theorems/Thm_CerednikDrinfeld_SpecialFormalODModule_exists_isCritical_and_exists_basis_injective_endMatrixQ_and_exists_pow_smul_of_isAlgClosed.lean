-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isCritical_and_exists_basis_injective_endMatrixQ_and_exists_pow_smul_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormalODModule.exists_isCritical_and_exists_basis_injective_endMatrixQ_and_exists_pow_smul_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/c052f9f6-4691-59e7-8da6-f22cac3a7f4d
-- title:
--   Critical index, mathbb Zₚ-basis and order embedding of End_{mathcal O_D}Φ
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, $j\colon W(\mathbb F_{p^2})\to k$ a ring homomorphism, and $\Phi$ a special formal $\mathcal O_D$-module over $k$ relative to $j$: a two-dimensional commutative formal group law $\Phi.F$ over $k$ carrying an additive–multiplicative action of $W(\mathbb F_{p^2})$ by law endomorphisms together with an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$, subject to the predicates `IsSpecial` for $j$ and `HasHeight 4`. Write $M$ for the Cartier module of $\Phi.F$ and, for $n\in\mathbb N$, $M_n$ for the graded piece: the subgroup of those $f\in M$ with $[\tau(c)]_*f=j(\tau(c))^{p^n}\cdot f$ for all $c\in\mathbb F_{p^2}$, $\tau$ the Teichmüller lift. The assertion is that there exists $i$ with $i=0$ or $i=1$ such that $i$ is critical, i.e. for every $m\in M_i$ the element $\varpi_*m$ lies in the image of the Verschiebung on $M$, and such that the $\mathbb Z_p$-module `invariantsSubmodule` of $M$ at $i$ admits a basis $\beta$ indexed by $\mathrm{Fin}\,2$ with: every $m\in M_i$ is uniquely $\sum_r w_r\cdot\beta_r$ with $w_r\in W(k)$; the ring homomorphism `endMatrixQ` from the centraliser of the $\mathcal O_D$-action and of $\varpi$ in $\operatorname{End}(\Phi.F)$ to $M_2(\mathbb Q_p)$ determined by $\beta$ is injective; and there is $m\in\mathbb N$ such that every matrix $p^mA$ with $A\in M_2(\mathbb Z_p)$ is a value of `endMatrixQ`, while $p^m$ times any value of `endMatrixQ` is integral.
--
--   This is the explicit form, at a critical index, of the identification of the $\mathcal O_D$-linear endomorphism ring of a special formal $\mathcal O_D$-module of height $4$ over an algebraically closed field with an order in $M_2(\mathbb Q_p)$, which is the source of the $GL_2(\mathbb Q_p)$-action in Drinfeld's representability theorem. It is used in the compatibility of such an embedding with rigidifications, via [`CerednikDrinfeld.FormalODModule.exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat`](thm.html#CerednikDrinfeld.FormalODModule.exists_pow_smul_map_eq_of_ringHom_centralizer_rigidification_compat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormalODModule_exists_isCritical_and_exists_basis_injective_endMatrixQ_and_exists_pow_smul_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Definitions.Def_CerednikDrinfeld_CritChartEndMatrix

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

theorem CerednikDrinfeld.SpecialFormalODModule.exists_isCritical_and_exists_basis_injective_endMatrixQ_and_exists_pow_smul_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
    (j : CerednikDrinfeld.Zp2 p →+* k) (Φ : CerednikDrinfeld.SpecialFormalODModule p j) :
    ∃ i : ℕ, (i = 0 ∨ i = 1) ∧ CritChart.IsCritical Φ.toFormalODModule j i ∧
      ∃ β : Module.Basis (Fin 2) ℤ_[p] (CritChart.invariantsSubmodule Φ.toFormalODModule j i),
        (∀ m ∈ Φ.gradedPiece j i, ∃! w : Fin 2 → WittVector p k,
          m = ∑ r, w r • (β r : MvFormalGroup.CartierModule p Φ.F)) ∧
        Function.Injective (CritChart.endMatrixQ Φ.toFormalODModule j i β) ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ e,
            CritChart.endMatrixQ Φ.toFormalODModule j i β e = (p : ℚ_[p]) ^ m • A.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p],
            (p : ℚ_[p]) ^ m • CritChart.endMatrixQ Φ.toFormalODModule j i β e = A.map ((↑) : ℤ_[p] → ℚ_[p])) := by sorry
