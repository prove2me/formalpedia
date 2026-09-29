-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAt_le_of_mem_cut
-- name    : AutomorphicForm.CuspidalConstituent.exists_forall_norm_foldr_archDerivAt_le_of_mem_cut
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/117fe561-9ab3-50c5-be0e-a421da8d8d44
-- title:
--   Iterated real-place flow derivatives are bounded on determinant shells
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D=\bigcup_{x\in T}\{g x : g\in\mathfrak{S}\}$, where $\mathfrak{S}$ is the centre-cut Siegel set of those $g$ whose finite part is integral, whose archimedean component at every infinite place has local height at least $c$ and $x$-window square at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$; assume $D$ covers modulo the centre, i.e. for each $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z\in D$. Consider the production pins over $D$ with level subgroups $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{heckeGen}_v$ and adelic box; their central group is all of $(\mathbb{A}_K)^\times$. Let $\xi$ be a character of that group, and $V$ a $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these pins and $\xi$: a cusp subrepresentation, non-zero, and minimal among non-zero cusp subrepresentations contained in it. Let $w_0\in\mathbb{R}$ with $\|\xi(z)\|=\|z\|_{\mathbb{A}}^{w_0}$ for all ideles, $N\neq 0$ an ideal, $\mathrm{tys}$ a family assigning to each infinite place finitely many archimedean types, and let $x$ lie in $V$, be invariant under right translation by the level-$N$ subgroup, and lie in the archimedean cut submodule of $\mathrm{tys}$. Let $w$ be a real infinite place, and $0<e_1<e_2$. Then for every word $l$ in the three flow directions $H,E,F^-$ there is $B\in\mathbb{R}$ with $\|(D_l x)(g)\|\le B$ whenever $\|\det g\|_{\mathbb{A}}\in[e_1,e_2]$, where $D_l$ is the iterated derivative at $t=0$ along the corresponding one-parameter flows at $w$. The proof shown uses neither $w_0$ and its modulus hypothesis nor the strict inequality $e_1<e_2$.
--
--   This is the statement that a $K$-finite, level-$N$, archimedean-type-cut vector in a cuspidal constituent has all of its iterated real-place Lie-algebra derivatives bounded on each determinant shell — the usual boundedness of cusp forms and their derivatives on Siegel sets. It supports the regularity requirements in the weight-one archimedean analysis, being cited in the construction of the $J$-rigid weight-one witness and in the computation of Whittaker coefficients for cuspidal constituents of weight one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_forall_norm_foldr_archDerivAt_le_of_mem_cut.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_forall_norm_foldr_archDerivAt_le_of_mem_cut
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w : InfinitePlace K) (hw : w.IsReal)
    (e₁ e₂ : ℝ) (he₁ : 0 < e₁) (he : e₁ < e₂) (l : List ArchDir) :
    ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
      ‖(l.foldr (archDerivAt hw) x) g‖ ≤ B := by sorry
