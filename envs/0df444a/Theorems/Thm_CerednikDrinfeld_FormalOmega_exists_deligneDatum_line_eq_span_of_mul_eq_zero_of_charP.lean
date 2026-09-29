-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP
-- name    : CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/f38d99e2-2e53-5128-86ce-c586ef59e4e4
-- title:
--   Deligne data over a characteristic-p field with prescribed edge lines
-- statement:
--   Let $p$ be a prime and let $\kappa$ be a field of characteristic $p$ equipped with a $\mathbb{Z}_p$-algebra structure. Let $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ be an element whose underlying matrix is $\operatorname{diag}(p,1)$, where $p$ is taken via $\mathbb{Z}_p \to \mathbb{Q}_p$, and let $c, c' \in \kappa$ satisfy $cc' = 0$, with each of $c$ and $c'$ either zero or not fixed by the $p$-power map (i.e. $c = 0$ or $c^p \neq c$, and likewise for $c'$). The assertion is that there exists a `DeligneDatum` $d$ for $\mathcal{O} = \mathbb{Z}_p$, $K = \mathbb{Q}_p$, uniformiser $p$ and coefficient ring $\kappa$ — that is, an assignment $M \mapsto d.\mathrm{line}(M)$ of a $\kappa$-submodule of $\kappa \otimes_{\mathbb{Z}_p} M$ to every full $\mathbb{Z}_p$-lattice $M \subset \mathbb{Q}_p^2$, such that each quotient $(\kappa \otimes_{\mathbb{Z}_p} M)/d.\mathrm{line}(M)$ is an invertible $\kappa$-module, the lines are compatible with inclusions of lattices, they are equivariant for scalar homotheties, and the nondegeneracy condition of the structure holds at every prime ideal of $\kappa$ — with the following two prescribed values on the standard edge. First, $d.\mathrm{line}$ of the standard lattice $\mathbb{Z}_p^2$ is the $\kappa$-span of $c \otimes e_0 + 1 \otimes e_1$; second, $d.\mathrm{line}$ of the lattice $g \cdot \mathbb{Z}_p^2$ is the image of the $\kappa$-span of $1 \otimes e_0 + c' \otimes e_1$ under the transport isomorphism $\kappa \otimes_{\mathbb{Z}_p} \mathbb{Z}_p^2 \cong \kappa \otimes_{\mathbb{Z}_p} (g\cdot\mathbb{Z}_p^2)$ induced by $g$.
--
--   This realises, over a field of characteristic $p$, the points of Drinfeld's formal $p$-adic upper half plane lying on the standard edge of the Bruhat–Tits tree of $\mathrm{GL}_2(\mathbb{Q}_p)$ whose coordinates in the edge chart $\{\xi\eta = 0\}$ avoid the $\mathbb{F}_p$-rational points other than the crossing: the node $c = c' = 0$, and the two branch cases in which exactly one of $c$, $c'$ is a non-$\mathbb{F}_p$ element. It is used in the construction of the corresponding special formal $\mathcal{O}_D$-modules, supplying the geometric-fibre input to the statements about Cartier quadruples on the standard edge.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlanePoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.exists_deligneDatum_line_eq_span_of_mul_eq_zero_of_charP
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
    (c c' : κ) (hcc' : c * c' = 0) (hc : c = 0 ∨ c ^ p ≠ c) (hc' : c' = 0 ∨ c' ^ p ≠ c') :
    ∃ d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ,
      d.line (stdFullLattice ℚ_[p]) =
          Submodule.span κ {c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1} ∧
        d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
          (Submodule.span κ {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + c' ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
            (actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap := by sorry
