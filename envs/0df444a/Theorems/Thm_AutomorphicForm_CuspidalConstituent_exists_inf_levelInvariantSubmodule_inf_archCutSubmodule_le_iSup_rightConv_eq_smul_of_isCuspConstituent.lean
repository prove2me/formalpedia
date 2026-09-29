-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/72158f8b-9251-5175-91bc-3de296da6811
-- title:
--   Finite eigencapture of a level-and-type cut of a cuspidal constituent
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$ such that the union $\mathfrak S=\bigcup_{x\in T}\{gx: g\in \mathrm{centreCutSiegelSet}\}$ of right translates of the centre-cut Siegel set — the set of $g$ whose finite part is integral, with local height at least $c$, window square at most $u^2$ and archimedean determinant norm in $[d_1,d_2]$ at every infinite place — satisfies `CoversModCentre`: every $g$ can be moved into $\mathfrak S$ by left multiplication by a global point of $\mathrm{GL}_2(F)$ and right multiplication by a central adelic scalar. Work with the pins `productionPinsOf` attached to $\mathfrak S$, with levels $U(N)=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}$ and adelic box $\mathrm{adelicBox}$; their central group is all of $(\mathbb{A}_F)^\times$, and $\xi$ is a homomorphism from it to $\mathbb{C}^\times$. Let $N\neq 0$ be an ideal of $\mathcal O_F$, let $\mathrm{tys}$ be an archimedean type family (a finite family of types at each infinite place), and let $V$ be a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ which is a cusp constituent: $V$ is a cuspidal subrepresentation, $V\neq 0$, and every cuspidal subrepresentation contained in $V$ is $0$ or $V$. Assume the cut $X=V\cap\{\varphi:\varphi(gu)=\varphi(g)\ \forall u\in U(N)\}\cap\mathrm{archCutSubmodule}(\mathrm{tys})$ is non-zero. Then there are a factorizable test function $f$ (a product of an archimedean and a finite test factor), an $n\in\mathbb{N}$, non-zero scalars $\lambda_1,\dots,\lambda_n\in\mathbb{C}$ and submodules $E_1,\dots,E_n$ of functions on $\mathrm{GL}_2(\mathbb{A}_F)$ such that each $\varphi\in E_i$ lies in the $K$-finite cuspidal space `cuspKFiniteSubmodule` for the pins and $\xi$ and satisfies $\varphi * f=\lambda_i\varphi$ for the right convolution against adelic $\mathrm{GL}_2$ Haar measure, and $X\le \bigvee_i E_i$.
--
--   This is the spectral step behind admissibility of cuspidal constituents: a single factorizable smoothing operator captures the level-$N$, type-$\mathrm{tys}$ cut of a cuspidal constituent inside finitely many of its non-zero eigenspaces. It is used to deduce finite-dimensionality of that cut in [`AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent`](thm.html#AutomorphicForm.finiteDimensional_inf_levelInvariantSubmodule_inf_archCutSubmodule_of_isCuspConstituent).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_inf_levelInvariantSubmodule_inf_archCutSubmodule_le_iSup_rightConv_eq_smul_of_isCuspConstituent
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁)
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hX : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≠ ⊥) :
    ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (_ : IsFactorizableTestFn F f) (n : ℕ) (lam : Fin n → ℂ)
      (_ : ∀ i, lam i ≠ 0) (E : Fin n → Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ i, ∀ φ ∈ E i, φ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ ∧ rightConv F φ f = lam i • φ) ∧
      V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ ⨆ i, E i := by sorry
