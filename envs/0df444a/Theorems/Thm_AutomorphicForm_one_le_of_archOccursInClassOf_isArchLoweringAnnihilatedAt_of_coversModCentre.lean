-- Prove2me | Theorems.Thm_AutomorphicForm_one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre
-- name    : AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/72afd0ae-e9d9-5f34-9a8b-1bac2d14e6c3
-- title:
--   Lowering-annihilated cusp forms at a real place have weight k ≥ 1
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$, where $\mathfrak{S}$ is the centre-cut Siegel set `centreCutSiegelSet F c u d₁ d₂`, consisting of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place has `localHeight` at least $c$ and `xWindowSq` at most $u^2$, and with `archDetNorm` at every infinite place in $[d_1,d_2]$. Assume $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ can be written so that $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(F)$ (via `globalPoints`) and some central scalar $z$ from $\mathbb{A}_F^\times$. Let $\Theta$ be a Hecke eigensystem over $F$ with complex coefficients (a nonzero level ideal together with families $a,b$ indexed by the height-one primes of $\mathcal{O}_F$), let $w$ be a real place of $F$, and let $k\in\mathbb{Z}$. Suppose the following occurs in the class of $\Theta$ on $D$: there is an eigensystem $\Theta'$ whose $a$- and $b$-values agree with those of $\Theta$ outside a finite set of primes, and a smooth cusp realisation $R'$ at the production pins built from $D$, the level-one groups intersected with the finite adelic subgroup, the Hecke generators and the adelic box, for the central renormalisation `Θ'.toRawCentral` (same level and $a$, with $b_v$ multiplied by $(\mathrm{cNorm}\,v)^{-1}$), which is genuine and whose underlying function $\varphi$ satisfies two conditions: $\varphi$ has, at $w$, the archimedean character `HasArchCharacterAt₀` given by the weight-$k$ character `archWeightCharℝ k` transported along the isomorphism $F_w\cong\mathbb{R}$, and $\varphi$ is annihilated by the lowering operator at $w$, i.e. for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ and every $z$ in the upper half-plane the real slice $m\mapsto\varphi\bigl(g\,\iota_w(m)\bigr)$ (extended by $0$ where $\det m=0$) is real-differentiable at $\begin{pmatrix}\operatorname{Im}z&\operatorname{Re}z\\0&1\end{pmatrix}$ and $\bigl(Df(m)(m\,\mathrm{diag}(1,-1))-i\,Df(m)(m\begin{pmatrix}0&1\\1&0\end{pmatrix})\bigr)/2$ vanishes there. Then $1\le k$.
--
--   This is the adelic form of the classical vanishing statement that there are no holomorphic cusp forms of non-positive weight: a lowest-weight (lowering-annihilated) vector of pure rotation type $k$ in the cuspidal spectrum at a real place must have $k\ge 1$, since otherwise the Casimir eigenvalue forces the realisation to be invariant under $\mathrm{SL}_2(\mathbb{R})$ at $w$ and hence zero by cuspidality. It serves as the base of the weight bookkeeping at a real place, feeding the weight-raising statement [`AutomorphicForm.archOccursInClassOf_archWeightChar_add_two_of_nonneg_of_coversModCentre`](thm.html#AutomorphicForm.archOccursInClassOf_archWeightChar_add_two_of_nonneg_of_coversModCentre), the $K$-type module criterion [`AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre`](thm.html#AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre) and the determination of admissible Casimir eigenvalues.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm

theorem AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ)
    (hk :
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
            ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
              (norm_ringEquivRealOfIsReal hw))) φ ∧
          IsArchLoweringAnnihilatedAt w hw φ)) :
    1 ≤ k := by sorry
