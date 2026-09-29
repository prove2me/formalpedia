-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar
-- name    : AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/a2733518-ec33-5ba9-855e-02b380e5a02f
-- title:
--   Type-χ vectors of a cyclic span lie in a spherical span
-- statement:
--   Let $F$ be a number field and, for each infinite place $w$ of $F$, let $\chi_w$ be a group homomorphism from `rowIsometrySubgroup₀ w.Completion` to $\mathbb{C}^\times$. Let $\Psi_1,\varphi : \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ with $\Psi_1$ continuous, and assume both $\Psi_1$ and $\varphi$ lie in `archCutSubmodule F (ArchTypeFamily.ofChar F χ)`, that is, in the intersection over the infinite places $w$ of the submodules `archTypeSubmoduleAt F w (ArchRepAt.ofChar F (χ w))` attached to the one-dimensional representation `charRep (χ w)`. Assume further that $\varphi$ lies in the $\mathbb{C}$-span of those $\psi$ for which there are $g$ in `finiteAdelicGL2Subgroup F`, the kernel of the archimedean projection `glArch`, and $k$ in the supremum of the ranges of the maps `rowIsometryInclAt₀ F w`, such that either $\psi = x\mapsto \Psi_1(x g k)$, or there are a function $f$ on $\mathrm{GL}_2(\mathbb{A}_F)$ and an arch type family `tys` with $f$ factorizable (a product of a compactly supported smooth-in-the-matrix-entries archimedean factor and a compactly supported locally constant finite factor) and `IsArchBiFinite F tys f`, and $\psi = x \mapsto (\Psi_1 * f)(xgk)$, where $(\Psi_1 * f)(y)=\int \Psi_1(yz) f(z)\,dz$ against the adelic Haar measure. The conclusion is that $\varphi$ lies in the sum of two submodules: the span of the finite-adelic right translates $x\mapsto\Psi_1(xg)$, $g$ in `finiteAdelicGL2Subgroup F`, and the span of the functions $x\mapsto(\Psi_1 * f)(xg)$ with $g$ in `finiteAdelicGL2Subgroup F` and $f(y)=f_\infty(\mathrm{glArch}\,y)\,f_{\mathrm{fin}}(\mathrm{glFin}\,y)$, where $f_\infty$ satisfies `IsArchTestFactor F` and `IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ)` and is invariant under conjugation by `archRowIsometryInclAt₀ F w k` for every infinite place $w$ and every $k$ in the row-isometry group at $w$, and $f_{\mathrm{fin}}$ is locally constant with compact support.
--
--   This is the isotypic-projection step in the comparison of two type-$\chi$ vectors inside a cuspidal constituent: it replaces an arbitrary presentation of $\varphi$ by translates and convolutes of $\Psi_1$, involving archimedean translates and arbitrary bi-finite test functions, by one using only finite-adelic translates and factorizable test functions whose archimedean factor is of type $\chi$ and spherical in the sense of being conjugation-invariant under each archimedean row-isometry group. It is used in the proof that a cuspidal constituent of finite-dimensional type is generated over the finite adeles by the translates of a single type-$\chi$ vector.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (Ψ₁ φ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ₁ : Continuous Ψ₁)
    (hχ₁ : Ψ₁ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (hχφ : φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (hφ : φ ∈ Submodule.span ℂ
      {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F (g * k) Ψ₁ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          ψ = rightTranslate F (g * k) (rightConv F Ψ₁ f)}) :
    φ ∈ Submodule.span ℂ ((fun g => rightTranslate F g Ψ₁) '' (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))) ⊔
      Submodule.span ℂ
        {ψ | ∃ g ∈ finiteAdelicGL2Subgroup F,
          ∃ (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ),
            IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) fa ∧
            (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
              fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
            IsFinTestFactor F ff ∧
            ψ = rightTranslate F g (rightConv F Ψ₁
              (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)))} := by sorry
