-- Prove2me | Theorems.Thm_AutomorphicForm_not_archOccursInClassOf_archWeightChar_sub_two_of_isArchLoweringAnnihilatedAt_of_coversModCentre
-- name    : AutomorphicForm.not_archOccursInClassOf_archWeightChar_sub_two_of_isArchLoweringAnnihilatedAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/34d30dbc-7d91-5be7-b4fe-c049eb8fd676
-- title:
--   No weight k-2 beneath a lowering-annihilated weight k
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\{gx : g\in\mathfrak{S}\}$, where $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in the integral subgroup, whose archimedean component at every infinite place has local height at least $c$ and window coordinate $\mathrm{xWindowSq}\le u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$. Assume `CoversModCentre F D`: for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ there are $\gamma\in\mathrm{GL}_2(F)$ and a central idele $z$ with $\gamma g z\in D$. Let $\Theta$ be a complex Hecke eigensystem over $F$ (a level ideal $\ne 0$ together with tables $a,b$ indexed by the finite places), let $w$ be a real infinite place and $k\in\mathbb{Z}$ with $k\ge 2$. Here a predicate $P$ on functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ "occurs in the class of $\Theta$ on $D$" (`ArchOccursInClassOf`) when some eigensystem $\Theta'$ agreeing with $\Theta$ at all but finitely many finite places, in both tables, admits a genuine smooth cusp realisation at the production pins built from $D$ (level groups $\mathrm{levelOne}\sqcap$ the finite adelic subgroup, Hecke generators, adelic box, full centre) for the recentred eigensystem $\Theta'.\mathrm{toRawCentral}$, whose underlying function satisfies $P$. Assume that the conjunction of two conditions occurs in the class of $\Theta$ on $D$: the function transforms under the project's rotation subgroup at $w$ by the weight-$k$ character transported along the isomorphism $F_w\cong\mathbb{R}$, and it is lowering-annihilated at $w$, i.e. for every $g$ and every $z$ in the upper half-plane the archimedean slice $m\mapsto\varphi(g\,\iota_w(m))$ is real-differentiable at $\begin{pmatrix}\mathrm{Im}\,z&\mathrm{Re}\,z\\0&1\end{pmatrix}$ and the lowering combination $\tfrac12(\partial_{m\,\mathrm{diag}(1,-1)}-i\,\partial_{m\,\mathrm{antidiag}(1,1)})$ vanishes there. The conclusion is that the single condition of transforming by the weight-$(k-2)$ character at $w$ does not occur in the class of $\Theta$ on $D$.
--
--   This is the unitarity gap below a lowest weight vector: if the local component at a real place $w$ has a lowering-annihilated vector of $\mathrm{SO}(2)$-type $k\ge 2$, it is the discrete series of weight $k$, whose types are $\pm k,\pm(k+2),\dots$, so the type $k-2$ is absent. It is used in the identification of the archimedean $K$-type module attached to such a class, and in the archimedean input to the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_not_archOccursInClassOf_archWeightChar_sub_two_of_isArchLoweringAnnihilatedAt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.not_archOccursInClassOf_archWeightChar_sub_two_of_isArchLoweringAnnihilatedAt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (w : InfinitePlace F) (hw : w.IsReal) (k : ℤ) (hk2 : 2 ≤ k)
    (hk :
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
            ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
              (norm_ringEquivRealOfIsReal hw))) φ ∧
          IsArchLoweringAnnihilatedAt w hw φ)) :
    ¬
      ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
        (fun φ => HasArchCharacterAt₀ F w
          ((archWeightCharℝ (k - 2)).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
            (norm_ringEquivRealOfIsReal hw))) φ) := by sorry
