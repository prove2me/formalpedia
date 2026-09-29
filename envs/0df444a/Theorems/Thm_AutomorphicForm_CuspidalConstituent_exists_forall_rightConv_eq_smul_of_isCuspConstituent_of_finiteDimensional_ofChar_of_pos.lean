-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/795dee48-c6ad-5535-b93a-324fbe63c0af
-- title:
--   Scalar action of conjugation-invariant test functions on a one-type cut
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $0<c$, $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\{gx : g\in \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\}$, where the latter consists of the $g$ whose finite part is integral, whose local height at every infinite place is at least $c$, whose window quantity $\mathrm{xWindowSq}$ is at most $u^2$ there, and whose archimedean determinant norms lie in $[d_1,d_2]$; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb{A}_F^\times$ with $\gamma g\,\mathrm{diag}(z,z)\in D$. Let $\mathrm{pins}$ be the production carrier pins built from $D$, the level family $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{diag}(\varpi_v,1)$ and the adelic box, so that its measures are the Borel Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$ and the additive Haar measure on $\mathbb{A}_F$ conditioned on the box, and its central subgroup is all of $\mathbb{A}_F^\times$; let $\xi$ be a character of that subgroup. Let $N\neq 0$ be an ideal of $\mathcal{O}_F$, and let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is a cuspidal constituent for $\mathrm{pins}$ and $\xi$: $V$ is contained in the $K$-finite cusp submodule, is stable under right translation by the finite adelic subgroup and by the archimedean row-isometry subgroups $\mathrm{rowIsometrySubgroup}_0$, is stable under right convolution by factorizable test functions that are archimedean bi-finite, is nonzero, and contains no such subrepresentation other than $0$ and $V$. Assume every infinite place of $F$ is real, and let $\chi=(\chi_w)_w$ be a family of characters $\mathrm{rowIsometrySubgroup}_0(F_w)\to\mathbb{C}^\times$. Assume the cut $X=V\cap\{\varphi : \varphi(gu)=\varphi(g)\ \forall u\in \mathrm{pins}.U\,N\}\cap \mathrm{archCutSubmodule}(\mathrm{ArchTypeFamily.ofChar}\,\chi)$, the last factor being the intersection over the infinite places of the $\chi_w$-type submodules, is finite-dimensional over $\mathbb{C}$. Let $f:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a factorizable test function, and assume there is $f_\infty$ on $\mathrm{GL}_2(\mathbb{A}_{F,\infty})$ which is smooth in the matrix entries with compact support, is archimedean factor bi-finite of type $\mathrm{ofChar}\,\chi$, is invariant under conjugation by $\mathrm{archRowIsometryInclAt}_0\,F\,w\,k$ for every infinite place $w$ and every $k$, and satisfies $f(g)=f_\infty(\mathrm{glArch}\,g)\cdot\mathbf{1}_{\mathrm{glFin}(\mathrm{pins}.U\,N)}(\mathrm{glFin}\,g)$. Then there is $\lambda\in\mathbb{C}$ such that $\mathrm{rightConv}\,F\,\varphi\,f=\lambda\varphi$ for every $\varphi\in X$, where $(\mathrm{rightConv}\,F\,\varphi\,f)(g)=\int \varphi(gx)f(x)\,d\mu(x)$ against the Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the multiplicity-one statement for characters of the archimedean row-isometry (circle) subgroups, in the form used for the adelic cuspidal constituents of this development: on the single-type, fixed-level cut of a cuspidal constituent, right convolution by a conjugation-invariant test function of type $\chi$ is a homothety. It is used in the proof that each such cut is spanned by the right translates, under the finite adelic group, of a single function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_forall_rightConv_eq_smul_of_isCuspConstituent_of_finiteDimensional_ofChar_of_pos
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hreal : ∀ w : InfinitePlace F, w.IsReal)
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hfin : FiniteDimensional ℂ
      ↥(V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓
        archCutSubmodule F (ArchTypeFamily.ofChar F χ)))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : ∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) fa ∧
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g)) :
    ∃ lam : ℂ, ∀ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓
        archCutSubmodule F (ArchTypeFamily.ofChar F χ), rightConv F φ f = lam • φ := by sorry
