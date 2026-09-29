-- Prove2me | Theorems.Thm_AutomorphicForm_isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/daec0c17-3def-5194-ba3c-9151f69050ed
-- title:
--   Isotypic cusp space on a covering window embeds into the slab domain space
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$ and adele ring $\mathbb{A}$, and let $G(\mathbb{A})$ denote $\mathrm{GL}_2(\mathbb{A})$. Fix reals $c,u,d_1,d_2$ with $d_1<d_2$, a finite set $T\subseteq G(\mathbb{A})$, and let $W=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet` is the set of $g$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component satisfies, at every infinite place $w$, `localHeight` $\ge c$, `xWindowSq` $\le u^2$ and `archDetNorm` $\in[d_1,d_2]$; assume `CoversModCentre`, i.e. every $g\in G(\mathbb{A})$ can be written so that $\gamma g z\in W$ for some $\gamma\in \mathrm{GL}_2(K)$ (via `globalPoints`) and some central scalar $z$ from $\mathbb{A}^\times$. Fix reals $\alpha>0$ and $\beta$, and a set $\Phi\subseteq\{g : \lVert\det g\rVert\in[\alpha,\beta]\}$ (idele norm in the sense of [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19)) that is a fundamental domain for the left action of the image of $\mathrm{GL}_2(K)$ on the restriction of the adelic Haar measure `adelicGLHaar` to that determinant slab. Fix further a family $N\mapsto U(N)$ of subgroups of $G(\mathbb{A})$, elements $\mathrm{gen}(v)\in G(\mathbb{A})$ indexed by the finite places, a set $B\subseteq\mathbb{A}$, a homomorphism $\xi$ from the full group $\mathbb{A}^\times$ (as the subgroup $\top$) to $\mathbb{C}^\times$, an ideal $N$, a finite set $S$ of finite places and a Hecke eigensystem $\pi$ over $\mathbb{C}$. Then the $\mathbb{C}$-span of the functions $\varphi : G(\mathbb{A})\to\mathbb{C}$ satisfying `IsIsotypicCuspFormAt` for the carrier data `productionPinsOf` with carrier set $W$ (Borel structures, adelic Haar measure on $G(\mathbb{A})$, central subgroup $\top$, the given $U$ and $\mathrm{gen}$, and the conditional additive Haar measure on $B$) is contained in the corresponding span for the same data with carrier set $\Phi$; that is, continuity, right $U(N)$-invariance, the Hecke eigenvalue conditions $\pi.a(v)$ and the central eigenvalue conditions $\pi$.`toRawCentral.b`$(v)$ for $v\notin S$ being unchanged, the smooth cuspidal automorphy condition relative to $W$ implies the one relative to $\Phi$.
--
--   This is the comparison step that transfers the isotypic cusp spaces from a finite union of translated centre-cut Siegel sets, which covers $\mathrm{GL}_2(\mathbb{A})$ modulo $\mathrm{GL}_2(K)$ and the centre, to a genuine fundamental domain inside a determinant slab; the two carrier data differ only in the set on which square-integrability is imposed. It is used in the trace and integral estimates for cut Hecke traces later in the construction of automorphic forms on $\mathrm{GL}_2$ over a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isotypicCuspSubmodule_le_of_coversModCentre_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (α β : ℝ) (hα : 0 < α)
    (Φ : Set (AdelicGL2 (𝓞 K) K))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K) (B : Set (AdeleRing (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (π : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K
        (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂) U gen B) ξ N S π ≤
      isotypicCuspSubmodule K (productionPinsOf K Φ U gen B) ξ N S π := by sorry
