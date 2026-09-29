-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets_principal
-- name    : AutomorphicForm.exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/459c1def-cf8b-5e31-9d32-183e76fc4c5e
-- title:
--   Finitely many cuspidal constituents meet a principal-level eigensystem
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $F$. Put $D=\bigcup_{x\in T}\{g x: g\in \mathfrak S\}$, where $\mathfrak S=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in the finite integral subgroup, whose archimedean components have local height at least $c$ and $x$-window square at most $u^2$ at every infinite place, and whose archimedean determinant norms all lie in $[d_1,d_2]$. Assume `CoversModCentre F D`: for every adelic $g$ there are $\gamma\in \mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\cdot 1\in D$. Let `pins` be `productionPinsOf` on $D$ with level groups $N\mapsto$ `principalLevel (𝓞 F) F N` intersected with the kernel of the archimedean projection, Hecke generators `heckeGen (𝓞 F) F v`, and the adelic box (so the centre subgroup is $\top$, the measures being adelic Haar on $\mathrm{GL}_2$ and additive adelic Haar conditioned on the box); let $\xi$ be a character of that centre, $N$ a nonzero ideal of $\mathcal O_F$, $S$ a finite set of finite places, and $\Psi$ a Hecke eigensystem over $\mathbb C$. Then there is a finite set $\mathcal V$ of $\mathbb C$-submodules of functions on $\mathrm{GL}_2$ of the adeles, each a cuspidal constituent for `pins` and $\xi$ (a nonzero submodule of the $K$-finite cuspidal submodule, stable under right translation by finite adelic matrices and by archimedean row isometries and under right convolution by factorizable archimedean-bifinite test functions, and minimal as such), with the property that every cuspidal constituent $V$ containing some nonzero $\varphi$ that is an isotypic cusp form for $(N,S,\Psi)$ — smooth cuspidal automorphic, continuous, right-invariant under the level group at $N$, a Hecke coset eigenfunction with eigenvalue $\Psi.a\,v$ for every $v\notin S$, and central eigen with eigenvalue $\Psi.b\,v$ there — satisfies $V\le\bigsqcup_{W\in\mathcal V}W$.
--
--   This is the finiteness half of strong multiplicity one in the form needed here: a cofinite Hecke eigensystem, together with the principal congruence level and central character, pins down the cuspidal constituents that can occur inside a finite family. It feeds the finite-dimensionality statement for the isotypic cuspidal submodule at principal level intersected with the archimedean cut submodule over a fundamental domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets_principal.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.exists_finset_isCuspConstituent_le_iSup_of_cuspConstituentMeets_principal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψ : HeckeEigensystem F ℂ) :
    ∃ 𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ W ∈ 𝒱, IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ W) ∧
      ∀ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
        IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ V →
        CuspConstituentMeets F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
            (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
            (adelicBox F)) ξ N S Ψ V →
          V ≤ ⨆ W ∈ 𝒱, W := by sorry
