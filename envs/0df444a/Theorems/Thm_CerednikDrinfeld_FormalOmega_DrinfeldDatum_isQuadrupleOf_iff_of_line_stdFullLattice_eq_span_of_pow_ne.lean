-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_stdFullLattice_eq_span_of_pow_ne
-- name    : CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_iff_of_line_stdFullLattice_eq_span_of_pow_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/8fb905fe-c2d5-5eff-b5ef-fd622f729c55
-- title:
--   Recognising the Drinfeld quadruple of a vertex-interior chart point
-- statement:
--   Fix a prime $p$ and a field $\kappa$ of characteristic $p$ that is a $\mathbb{Z}_p$-algebra, and let $c \in \kappa$ satisfy $c^p \neq c$. Let $d$ be a Deligne datum over $\kappa$ for the discrete valuation ring $\mathbb{Z}_p \subset \mathbb{Q}_p$ with uniformiser $p$, that is, a rule assigning to every full $\mathbb{Z}_p$-lattice $M \subset \mathbb{Q}_p^2$ a $\kappa$-submodule $d.\mathrm{line}(M)$ of $\kappa \otimes_{\mathbb{Z}_p} M$ with invertible quotient, compatible with inclusions and with homotheties, and satisfying the nondegeneracy condition at every prime of $\kappa$; assume that at the standard lattice $M = \mathbb{Z}_p^2$ the line is the $\kappa$-span of $c \otimes e_0 + 1 \otimes e_1$, where $e_0, e_1$ is the standard basis. Let $Q$ be a Drinfeld datum over $\kappa$ for the same data (two families $N_0, N_1$ of full lattices indexed by $\operatorname{Spec} \kappa$ with $N_0 \le N_1$ and $p N_1 \subseteq N_0$, invertible modules $T_0, T_1$ with maps $\Pi_0, \Pi_1$ composing to multiplication by $p$, and compatible surjections $u_0, u_1$ from the base-changed lattices to the stalks), and let $x$ be a point of $\operatorname{Spec} \kappa$. Then the predicate `IsQuadrupleOf` holds for $Q$ and $d$ — i.e. at every prime the pair $(Q.L_0, Q.L_1)$ satisfies `EdgeNondegAt` for $d$ and the kernels of $u_0$, $u_1$ are the lines of the Deligne datum obtained from $d$ by base change to the local ring, evaluated at $Q.L_0$, $Q.L_1$ — if and only if there are equalities $h_0 : N_0(x) = \mathbb{Z}_p^2$ and $h_1 : N_1(x) = p^{-1}\mathbb{Z}_p^2$ (the image of the standard lattice under the scalar matrix $p^{-1}$) such that, with $\kappa_x$ the localisation of $\kappa$ at the prime of $x$, the kernel of $u_0(x)$ is the $\kappa_x$-span of $c \otimes e_0 + 1 \otimes e_1$ transported along $h_0$, and the kernel of $u_1(x)$ is the $\kappa_x$-span of the image of that element under the scalar-matrix base-change isomorphism, transported along $h_1$.
--
--   This is the recognition step in the Čerednik–Drinfeld comparison: it pins down, over a field, the Drinfeld quadruples whose associated Deligne datum is a prescribed point lying in the interior of the vertex $[\mathbb{Z}_p^2]$ of the standard edge chart, the condition $c^p \neq c$ expressing that the chart line is not $\mathbb{F}_p$-rational. It is used in the construction of Cartier quadruples with prescribed line along an edge isogeny.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_DrinfeldDatum_isQuadrupleOf_iff_of_line_stdFullLattice_eq_span_of_pow_ne.lean

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

theorem CerednikDrinfeld.FormalOmega.DrinfeldDatum.isQuadrupleOf_iff_of_line_stdFullLattice_eq_span_of_pow_ne
    (p : ℕ) [Fact p.Prime] {κ : Type} [Field κ] [CharP κ p] [Algebra ℤ_[p] κ]
    (c : κ) (hc : c ^ p ≠ c)
    (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) κ)
    (hd : d.line (stdFullLattice ℚ_[p]) =
      Submodule.span κ {c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : κ) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1})
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) κ) (x : PrimeSpectrum κ) :
    Q.IsQuadrupleOf d ↔
      ∃ (h₀ : Q.N₀ x = (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p]).1)
        (h₁ : Q.N₁ x = (FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
          (stdFullLattice (𝒪 := ℤ_[p]) ℚ_[p])).1),
        LinearMap.ker (Q.u₀ x) = Submodule.span (locRing κ x)
          {transportEquiv (locRing κ x) (M₁ := stdFullLattice ℚ_[p]) (M₂ := Q.L₀ x) h₀.symm
            (algebraMap κ (locRing κ x) c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1)} ∧
        LinearMap.ker (Q.u₁ x) = Submodule.span (locRing κ x)
          {transportEquiv (locRing κ x)
              (M₁ := FullLattice.act (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
                (stdFullLattice ℚ_[p])) (M₂ := Q.L₁ x) h₁.symm
            (actBaseChange (locRing κ x) (scalarGL (unitOfNeZero (K := ℚ_[p]) (PadicInt.irreducible_p (p := p)).ne_zero)⁻¹)
              (stdFullLattice ℚ_[p])
              (algebraMap κ (locRing κ x) c ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 0 + (1 : locRing κ x) ⊗ₜ[ℤ_[p]] stdBasisVec ℚ_[p] 1))} := by sorry
