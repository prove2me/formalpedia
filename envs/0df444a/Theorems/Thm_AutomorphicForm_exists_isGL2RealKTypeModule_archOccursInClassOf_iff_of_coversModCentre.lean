-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isGL2RealKTypeModule_archOccursInClassOf_iff_of_coversModCentre
-- name    : AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/4b6a3f5c-b2eb-5afa-be10-a5de99cfc3ba
-- title:
--   Archimedean K-type profile of a cuspidal class at a real place
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be reals with $d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$. Put $D=\bigcup_{x\in T}\{gx : g\in \mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\}$, where the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place has local height $\ge c$ and $x$-window square $\le u^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for all $w$. Assume `CoversModCentre`: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ can be written $\gamma g z\in D$ with $\gamma\in\mathrm{GL}_2(F)$ and $z$ a central adelic scalar. Let $\Theta$ be a Hecke eigensystem over $F$ with complex coefficients (a nonzero level ideal together with two functions $a,b$ on the height-one spectrum of $\mathcal{O}_F$), and assume $\Theta$ occurs in the sense of `ArchOccursInClassOf` for the trivial predicate: some eigensystem $\Theta'$ agreeing with $\Theta$ away from finitely many places admits a smooth cusp realisation $R'$ of $\Theta'.\mathrm{toRawCentral}$ (the eigensystem with $b$ rescaled by $(\mathrm{cNorm}\,v)^{-1}$) at the production pins built on $D$, which is a genuine cusp realisation. Fix a real place $w$ of $F$. Then there exist a complex vector space $M$, a family $wt:\mathbb{Z}\to$ submodules of $M$ and linear maps $E,L,\varepsilon$ on $M$ such that: $(wt,E,L,\varepsilon)$ is a `IsGL2RealKTypeModule`, i.e. $wt$ is an internal direct sum decomposition of $M$, $E(wt\,n)\subseteq wt(n+2)$, $L(wt\,n)\subseteq wt(n-2)$, $E(Lv)-L(Ev)=n\,v$ for $v\in wt\,n$, $\varepsilon(wt\,n)\subseteq wt(-n)$, $\varepsilon^2=\mathrm{id}$ and $\varepsilon\circ E=L\circ\varepsilon$; each $wt\,n$ is finite-dimensional; the module is irreducible in the sense that $M\ne 0$ and every submodule $W$ with $W\le\bigsqcup_n (W\sqcap wt\,n)$ stable under $E,L,\varepsilon$ is $\bot$ or $\top$; the set of $n$ with $wt\,n\ne\bot$ is infinite; for every $n$, the property `HasArchCharacterAt₀` at $w$ for the character obtained from `archWeightCharℝ n` transported along the isomorphism $F_w\cong\mathbb{R}$ occurs in the class of $\Theta$ on $D$ if and only if $wt\,n\ne\bot$; and for every $k$, the conjunction of that property for $k$ with `IsArchLowestWeightAt` (for some $\sigma\in\mathbb{C}$, all functions $z\mapsto (\operatorname{Im}z)^{\sigma}\varphi(g\,\iota_w(\text{Iwasawa section of }z))$ on the upper half-plane are holomorphic) occurs in the class if and only if there is a nonzero $v\in wt\,k$ with $Lv=0$.
--
--   This identifies the archimedean profile at a real place $w$ of a cuspidally realised near-equivalence class — which rotation weights occur, and which occur together with a lowest-weight vector — with the $K$-type profile of a single irreducible admissible $(\mathfrak{g},K)$-module for $\mathrm{GL}_2(\mathbb{R})$, realised here through the $E,L,\varepsilon$ formalism. It feeds the dichotomy between parity-constrained and discrete-series archimedean behaviour used downstream.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isGL2RealKTypeModule_archOccursInClassOf_iff_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLowestWeight
import Definitions.Def_AutomorphicForm_GL2RealKTypeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (hΘ : ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ (fun _ => True))
    (w : InfinitePlace F) (hw : w.IsReal) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module ℂ M) (wt : ℤ → Submodule ℂ M)
      (E L ε : M →ₗ[ℂ] M),
      IsGL2RealKTypeModule wt E L ε ∧ (∀ n : ℤ, FiniteDimensional ℂ (wt n)) ∧
      IsIrreducibleGL2RealKTypeModule wt E L ε ∧ {n : ℤ | wt n ≠ ⊥}.Infinite ∧
      (∀ n : ℤ,
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
            (fun φ => HasArchCharacterAt₀ F w
              ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                (norm_ringEquivRealOfIsReal hw))) φ) ↔
          wt n ≠ ⊥) ∧
      (∀ k : ℤ,
        ArchOccursInClassOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ
            (fun φ => HasArchCharacterAt₀ F w
                ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw)
                  (norm_ringEquivRealOfIsReal hw))) φ ∧
              IsArchLowestWeightAt w hw φ) ↔
          ∃ v ∈ wt k, v ≠ 0 ∧ L v = 0) := by sorry
