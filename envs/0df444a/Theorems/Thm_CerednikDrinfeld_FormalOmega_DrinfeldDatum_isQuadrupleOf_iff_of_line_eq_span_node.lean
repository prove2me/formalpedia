-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_iff_of_line_eq_span_node
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/cba4f447-eec4-5ffe-b48f-2ad2447eeff5
-- title:
--   Recognising the node quadruple of the standard edge chart
-- statement:
--   Let $p$ be a prime and let $\kappa$ be a field of characteristic $p$ which is a $\mathbb{Z}_p$-algebra, and let $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ have underlying matrix $\mathrm{diag}(p,1)$. Let $d$ be a Deligne datum over $\kappa$ for the base field $\mathbb{Q}_p$ and uniformizer $p \in \mathbb{Z}_p$, i.e. a family of $\kappa$-submodules $d.\mathrm{line}\,M \subseteq \kappa \otimes_{\mathbb{Z}_p} M$ with invertible quotients, monotone in $M$, equivariant for homotheties and nondegenerate at every prime. Assume $d.\mathrm{line}$ at the standard lattice $\mathbb{Z}_p^2$ is the $\kappa$-span of $0 \otimes e_0 + 1 \otimes e_1$, and at $g\,\mathbb{Z}_p^2$ is the image of the span of $1 \otimes e_0 + 0 \otimes e_1$ under the base-changed transport isomorphism `actBaseChange` along $g$. Let $Q$ be a Drinfeld datum over $\kappa$ for the same uniformizer (lattices $N_0 \subseteq N_1$ with $p N_1 \subseteq N_0$, varying continuously over $\operatorname{Spec}\kappa$, invertible modules $T_0, T_1$ with maps $\Pi_0, \Pi_1$ composing to multiplication by $p$, and $\kappa_x$-linear maps $u_0, u_1$ from the base-changed lattices to the stalks), and let $x$ be a prime of $\kappa$. The assertion is that $Q$ satisfies `IsQuadrupleOf d` — at every prime the pair $(Q.L_0, Q.L_1)$ satisfies `DeligneDatum.EdgeNondegAt` for $d$ and the kernels of $u_0$, $u_1$ are the lines of the base change of $d$ to the local ring at that prime — if and only if there are equalities $h_0 : N_0(x) = \mathbb{Z}_p^2$ and $h_1 : N_1(x) = p^{-1} g\, \mathbb{Z}_p^2$ (the scalar matrix $p^{-1}$ acting on $g\,\mathbb{Z}_p^2$) such that $\ker u_0(x)$ is the $\kappa_x$-span of the transport along $h_0$ of $0 \otimes e_0 + 1 \otimes e_1$, and $\ker u_1(x)$ is the $\kappa_x$-span of the transport along $h_1$ of the image of $1 \otimes e_0 + 0 \otimes e_1$ under the successive transport isomorphisms for $g$ and for $p^{-1}$.
--
--   This is a recognition criterion in the Čerednik–Drinfeld theory: it identifies, over a field, exactly which Drinfeld quadruples correspond to the node of the standard edge chart of the formal upper half plane, by normalising the two lattices to $\mathbb{Z}_p^2$ and $\mathbb{Z}_p \oplus p^{-1}\mathbb{Z}_p$ and the two stalk kernels to the coordinate lines. It is used in the comparison with the moduli description of special formal $\mathcal{O}_D$-modules, via [`CerednikDrinfeld.FormalODModule.forall_isCartierQuadruple_map_node_line_eq_of_rigidNum_single_eq`](thm.html#CerednikDrinfeld.FormalODModule.forall_isCartierQuadruple_map_node_line_eq_of_rigidNum_single_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_eq_span_node.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_iff_of_line_eq_span_node
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p])
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = Matrix.diagonal ![algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]), 1])
    (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hd0 : d.line (stdFullLattice ℚ_[p]) =
      Submodule.span κ {(0 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1})
    (hd1 : d.line (FullLattice.act g (stdFullLattice ℚ_[p])) =
      (Submodule.span κ {(1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (0 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1}).map
        (actBaseChange κ g (stdFullLattice ℚ_[p])).toLinearMap)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ) (x : PrimeSpectrum κ) :
    Q.IsQuadrupleOf d ↔
      ∃ (h₀ : Q.N₀ x = (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1)
        (h₁ : Q.N₁ x = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (FullLattice.act g (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]))).1),
        LinearMap.ker (Q.u₀ x) = Submodule.span (locRing κ x)
          {transportEquiv (locRing κ x) (M₁ := stdFullLattice ℚ_[p]) (M₂ := Q.L₀ x) h₀.symm
            ((0 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)} ∧
        LinearMap.ker (Q.u₁ x) = Submodule.span (locRing κ x)
          {transportEquiv (locRing κ x)
              (M₁ := FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
                (FullLattice.act g (stdFullLattice ℚ_[p]))) (M₂ := Q.L₁ x) h₁.symm
            (actBaseChange (locRing κ x) (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
              (FullLattice.act g (stdFullLattice ℚ_[p]))
              (actBaseChange (locRing κ x) g (stdFullLattice ℚ_[p])
                ((1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (0 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)))} := by sorry
