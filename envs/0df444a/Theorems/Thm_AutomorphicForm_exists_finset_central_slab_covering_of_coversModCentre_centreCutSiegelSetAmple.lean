-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple
-- name    : AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/e8b08edb-6301-5734-8e81-710220f7d2da
-- title:
--   Finite central covering of determinant-norm slabs
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,\kappa$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, where $\mathbb{A}_F$ is the adele ring of $F$ over $\mathcal{O}_F$. Write $\mathfrak{S}=\mathtt{centreCutSiegelSetAmple}\,F\,c\,u\,d_1\,d_2\,\kappa$ for the set of $g\in\mathrm{GL}_2(\mathbb{A}_F)$ such that the finite part of $g$ lies in `finiteIntegralGL2`, at every infinite place $w$ the local height $\mathrm{h}_w(g)=|\det g_w|/\mathrm{rowNormSq}(g_w)$ of the archimedean component satisfies $c\le \mathrm{h}_w(g)$, the squared $x$-window at $w$ is at most $u^2$, the quantity $\mathtt{archDetNorm}\,w\,g$ lies in $[d_1,d_2]$, and $\mathrm{h}_w(g)\le\kappa\,\mathrm{h}_{w'}(g)$ for all pairs of infinite places $w,w'$. Put $D=\bigcup_{x\in T}\mathfrak{S}x$ and assume $D$ satisfies `CoversModCentre`: for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ there are $\gamma\in\mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g\,\mathrm{diag}(z,z)\in D$, the image of $\gamma$ being taken under `globalPoints` and the central scalar under `centralScalar`. Then for all reals $a,b$ with $0<a$ there is a finite set $N$ of ideles of $F$ such that every $g$ whose determinant has idele norm $\mathtt{ideleNorm}\,F(\det g)$ (the value at $\det g$ of the distributive Haar character of $\mathbb{A}_F$, as a real number) in $[a,b]$ admits $\gamma\in\mathrm{GL}_2(F)$ and $n\in N$ with $\gamma g\in D\,\mathrm{diag}(n,n)$.
--
--   This is the step that makes the central translation in a covering of $\mathrm{GL}_2(\mathbb{A}_F)$ modulo $\mathrm{GL}_2(F)$ and the centre uniform over a slab $a\le\|\det g\|\le b$ of determinant norms: finitely many central ideles suffice for the whole slab. It is used in the volume and integral estimates attached to ample centre-cut Siegel windows, in particular in the comparisons of integrals over slab fundamental domains and in the construction of ample coverings with prescribed realisations and approximation properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.exists_finset_central_slab_covering_of_coversModCentre_centreCutSiegelSetAmple
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)) :
    ∀ a b : ℝ, 0 < a → ∃ N : Finset (AdeleRing (𝓞 F) F)ˣ, ∀ g : AdelicGL2 (𝓞 F) F,
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b →
        ∃ γ : GL (Fin 2) F, ∃ n ∈ N,
          globalPoints (𝓞 F) F γ * g ∈
            (· * centralScalar (𝓞 F) F n) '' (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ) := by sorry
