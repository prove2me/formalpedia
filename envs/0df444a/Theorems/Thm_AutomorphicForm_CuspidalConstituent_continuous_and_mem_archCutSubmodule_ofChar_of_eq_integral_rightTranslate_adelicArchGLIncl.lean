-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl
-- name    : AutomorphicForm.CuspidalConstituent.continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/9523daa1-b252-57ab-aef8-b3fd72c59759
-- title:
--   Character projector onto the archimedean χ-type
-- statement:
--   Let $F$ be a number field. For each infinite place $w$ of $F$ let $\chi_w$ be a monoid homomorphism from the group `rowIsometrySubgroup₀ w.Completion` $\subseteq \mathrm{GL}_2(F_w)$ to $\mathbb{C}^\times$, assumed continuous as a $\mathbb{C}$-valued function; write $\mathcal K = \prod_w$ `rowIsometrySubgroup₀ w.Completion`, equipped with a measurable space structure that is the Borel structure of its topology, and let $\mu$ be a probability measure on $\mathcal K$ invariant under both left and right translation. Let $\iota : \mathcal K \to \mathrm{GL}_2(F_\infty)$ be a monoid homomorphism such that for all $\kappa$ and $w$ the image of $\iota(\kappa)$ under the map of general linear groups induced by evaluation at $w$, `archComponent F w`, is $\kappa_w$. Let $P$ be an operator on functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfying, for all $\varphi$ and all $x$, $$(P\varphi)(x) = \int_{\mathcal K} \Big(\prod_w \chi_w(\kappa_w)^{-1}\Big)\,\varphi\big(x\cdot \mathrm{incl}(\iota(\kappa))\big)\,d\mu(\kappa),$$ where $\mathrm{incl} =$ `adelicArchGLIncl F` is the embedding of $\mathrm{GL}_2(F_\infty)$ into $\mathrm{GL}_2(\mathbb{A}_F)$ with identity finite part. Then for every continuous $\varphi$ the following seven assertions hold: $P\varphi$ is continuous; $P\varphi$ lies in `archCutSubmodule F (ArchTypeFamily.ofChar F χ)`, i.e. in the intersection over all $w$ of the submodule of functions of type `charRep (χ w)` (the one-dimensional scalar representation attached to $\chi_w$) along `rowIsometryInclAt₀ F w`; if $\varphi$ already lies in that submodule then $P\varphi = \varphi$; for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ commuting with every $\mathrm{incl}(\iota(\kappa))$, $P$ commutes with right translation by $g$, where $(\mathrm{rightTranslate}\,g\,\varphi)(x) = \varphi(xg)$; for every $\kappa \in \mathcal K$, $P(\mathrm{rightTranslate}\,\mathrm{incl}(\iota(\kappa))\,\varphi) = \big(\prod_w \chi_w(\kappa_w)\big)\cdot P\varphi$; $P(\varphi + \psi) = P\varphi + P\psi$ for every continuous $\psi$; and $P(c\varphi) = c\,P\varphi$ for every $c \in \mathbb{C}$.
--
--   This is the isotypic projector of the compact group $\mathcal K = \prod_w K_w$ acting by right translation, cutting out the $\chi$-type component of a continuous function on $\mathrm{GL}_2(\mathbb{A}_F)$; continuity of $\varphi$ ensures the defining integrals are genuine. It is used to split the cyclic span of a vector of archimedean type $\chi$ into its type-$\chi$ part, and is invoked in the analysis of spans of right translates and of irreducible constituents of the relevant representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.continuous_and_mem_archCutSubmodule_ofChar_of_eq_integral_rightTranslate_adelicArchGLIncl
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ))
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ))
    (hP : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F),
      P φ x = ∫ κ, (∏ w, ((χ w (κ w)⁻¹ : ℂˣ) : ℂ)) * φ (x * adelicArchGLIncl F (ι κ)) ∂μ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    Continuous (P φ) ∧
    P φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) ∧
    (φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) → P φ = φ) ∧
    (∀ g : AdelicGL2 (𝓞 F) F, (∀ κ, g * adelicArchGLIncl F (ι κ) = adelicArchGLIncl F (ι κ) * g) →
      P (rightTranslate F g φ) = rightTranslate F g (P φ)) ∧
    (∀ κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion,
      P (rightTranslate F (adelicArchGLIncl F (ι κ)) φ) = (∏ w, ((χ w (κ w) : ℂˣ) : ℂ)) • P φ) ∧
    (∀ ψ : AdelicGL2 (𝓞 F) F → ℂ, Continuous ψ → P (φ + ψ) = P φ + P ψ) ∧
    (∀ c : ℂ, P (c • φ) = c • P φ) := by sorry
