-- Prove2me | Theorems.Thm_AutomorphicForm_archOccursInClassOf_hasArchCharacterAtZero_archCasimirAt_iff_twist_rpow_absNorm
-- name    : AutomorphicForm.archOccursInClassOf_hasArchCharacterAtZero_archCasimirAt_iff_twist_rpow_absNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/284ad144-4734-58f3-a605-7b0ac18da8b3
-- title:
--   Norm twists preserve archimedean occurrence in a cuspidal class
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<d_1$, let $T$ be a finite subset of the adelic group $\mathrm{GL}_2(\mathbb{A}_F)$, let $\Theta$ be a Hecke eigensystem over $F$ with complex coefficients (a nonzero level ideal of $\mathcal O_F$ together with families $a_v,b_v\in\mathbb C$ indexed by the height-one primes of $\mathcal O_F$), let $w$ be an infinite place of $F$ with $hw$ a witness that $w$ is real, and let $n\in\mathbb Z$, $\lambda\in\mathbb C$, $t\in\mathbb R$. Write $D=\bigcup_{x\in T}\,\{gx : g\in \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\}$, where the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean components satisfy $c\le$ `localHeight` and `xWindowSq` $\le u^2$ at every infinite place, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all infinite $w$. Let $P$ be the property of a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_F)$ that: $\varphi$ satisfies the predicate `HasArchCharacterAt₀` at $w$ for the character of the row-isometry subgroup at $w$ obtained by composing the weight-$n$ character `archWeightCharℝ n` with `rowIsometrySubgroup₀Map` along the norm-preserving ring isomorphism `ringEquivRealOfIsReal hw` of the completion $F_w$ with $\mathbb R$ (the analogue, for this subgroup, of the condition $\varphi(g k)=\chi(k)\varphi(g)$ imposed by `HasArchCharacterAt`); $\varphi$ is `IsArchSmoothAt` at $w$, i.e. for every $g$ the function $e\mapsto\varphi(g\cdot\mathrm{archRealLiftAt}\,hw\,e)$ is $C^\infty$ on the set of real $2\times2$ matrices of nonzero determinant; and $\varphi$ is an eigenfunction of the archimedean Casimir operator at $w$, $\mathrm{archCasimirAt}\,hw\,\varphi=\lambda\cdot\varphi$, where this operator is $-\bigl(\tfrac14 H^2-\tfrac12 H+EF^-\bigr)$ in the one-parameter flow derivatives `archDerivAt` at $w$. The theorem asserts that $P$ occurs in the class of $\Theta$ on $D$ in the sense of `ArchOccursInClassOf` — that is, there are an eigensystem $\Theta'$ agreeing with $\Theta$ away from finitely many primes and a smooth cusp realisation $R'$ for $\Theta'.\mathrm{toRawCentral}$ (same level and $a_v$, with $b_v$ replaced by $c_v^{-1}b_v$) over the production pins of $D$ formed with the level subgroups $\mathrm{levelOne}(N)\sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators `heckeGen` and the adelic box, such that $R'$ is a genuine cusp realisation and $P$ holds of its underlying function — if and only if the same holds for the twist of $\Theta$ by the character $v\mapsto \mathrm{N}(v)^{-t}$, i.e. for the eigensystem with the same level, $a_v$ replaced by $\mathrm{N}(v)^{-t}a_v$ and $b_v$ by $\mathrm{N}(v)^{-2t}b_v$, where $\mathrm{N}(v)$ is the absolute norm of the prime.
--
--   The statement records that the archimedean data singled out here — the weight-$n$ transformation law under the row-isometry subgroup at a real place, archimedean smoothness, and the Casimir eigenvalue $\lambda$ — are insensitive to twisting a Hecke eigensystem by an unramified power of the absolute norm, the corresponding realisations differing by the factor $\lVert\det\rVert^{t}$. It is used in the Langlands–Tunnell part of the development, in the transfer of such a witness through formal base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archOccursInClassOf_hasArchCharacterAtZero_archCasimirAt_iff_twist_rpow_absNorm.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.archOccursInClassOf_hasArchCharacterAtZero_archCasimirAt_iff_twist_rpow_absNorm
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd₁ : 0 < d₁)
    (Θ : HeckeEigensystem F ℂ) (w : InfinitePlace F) (hw : w.IsReal) (n : ℤ) (lam : ℂ) (t : ℝ) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ) ↔
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (Θ.twist (fun v : HeightOneSpectrum (𝓞 F) => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)))
        (fun φ => HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ ∧
            IsArchSmoothAt hw φ ∧ archCasimirAt hw φ = (lam) • φ) := by sorry
