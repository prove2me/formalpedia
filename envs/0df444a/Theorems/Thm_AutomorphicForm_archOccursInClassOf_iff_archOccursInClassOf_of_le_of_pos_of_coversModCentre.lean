-- Prove2me | Theorems.Thm_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre
-- name    : AutomorphicForm.archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/58f61a0d-43d8-5c92-b95c-c01e65886d45
-- title:
--   Occurrence in a Hecke class is independent of the determinant floor
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_1',d_2$ be real numbers and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, where $\mathbb{A}_F$ is the adele ring of $\mathcal{O}_F$ in $F$. For parameters $(c,u,d_1,d_2)$ the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2` and whose archimedean component at every infinite place $w$ has $c \le$ `localHeight`, `xWindowSq` $\le u^2$, and `archDetNorm` $w\,g \in [d_1,d_2]$; write $D$ and $D'$ for the unions $\bigcup_{x \in T}$ of its right translates by $x$, formed with floors $d_1$ and $d_1'$ respectively, the ceiling $d_2$ and $c,u$ being common. Assume $d_1 \le d_1'$, $0 < d_1'$ and $d_1' < d_2$, and that $D$ covers modulo the centre: every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ satisfies $\gamma g z \in D$ for some $\gamma \in \mathrm{GL}_2(F)$ and some central scalar $z$ from $\mathbb{A}_F^{\times}$. Let $\Theta$ be a Hecke eigensystem over $F$ with complex coefficients (a nonzero level ideal together with tables $a,b$ indexed by the height-one primes of $\mathcal{O}_F$), and let $P$ be an arbitrary predicate on functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$. For a window $E$, the relation `ArchOccursInClassOf F E Θ P` asserts the existence of an eigensystem $\Theta'$ whose tables $a$ and $b$ agree with those of $\Theta$ outside a finite set of primes, together with a smooth cusp realization at the production pins attached to $E$ (Borel subgroup and adelic Haar measure on $\mathrm{GL}_2$, full central subgroup, level subgroups $N \mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`, and the adelic box conditioning measure) for the twisted system $\Theta'$`.toRawCentral` (same level and $a$, with $b$ at $v$ divided by `cNorm` $v$) which is genuine, i.e. whose underlying function is continuous, and whose function satisfies $P$. Assuming `ArchOccursInClassOf` holds for $D$, $\Theta$ and the trivially true predicate, the conclusion is that `ArchOccursInClassOf` holds for $D'$, $\Theta$ and $P$ if and only if it holds for $D$, $\Theta$ and $P$.
--
--   This is the statement that the class of archimedean occurrence data attached to a Hecke eigensystem is insensitive to raising the lower bound on the archimedean determinant norms in the defining window, provided the larger window still covers $\mathrm{GL}_2(\mathbb{A}_F)$ modulo $\mathrm{GL}_2(F)$ and the centre and already supports a continuous realization. It is used in the comparison of occurrence on differently normalised Siegel windows, feeding the archimedean lowering step for weight-character shifts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering

theorem AutomorphicForm.archOccursInClassOf_iff_archOccursInClassOf_of_le_of_pos_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₁' d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hle : d₁ ≤ d₁') (hd₁' : 0 < d₁') (hd' : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (P : (AdelicGL2 (𝓞 F) F → ℂ) → Prop) :
    ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) Θ P ↔
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ P := by sorry
