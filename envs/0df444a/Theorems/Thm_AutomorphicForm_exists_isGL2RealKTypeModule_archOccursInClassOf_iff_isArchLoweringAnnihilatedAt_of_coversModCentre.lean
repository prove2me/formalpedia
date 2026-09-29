-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre
-- name    : AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/def2a9ee-0cf1-52f1-9606-428268fddd0b
-- title:
--   Real-place types of a Hecke class form an irreducible K-type module
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, and let $T$ be a finite set of elements of $\mathrm{GL}_2(\mathbb{A}_F)$; write $D=\bigcup_{x\in T}\{g x : g\in \mathfrak{S}\}$ for the union of the right translates by $T$ of the centre-cut Siegel set $\mathfrak{S}=$ `centreCutSiegelSet F c u d₁ d₂`, consisting of those $g$ whose finite part is integral, whose archimedean component at every infinite place has local height at least $c$ and squared $x$-window at most $u^2$, and with $\mathrm{archDetNorm}_w(g)\in[d_1,d_2]$ for every infinite place $w$. Assume $D$ covers modulo the centre: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and a unit ideles $z$ with $\gamma g\,z\in D$ (the global point and the central scalar being taken in $\mathrm{GL}_2(\mathbb{A}_F)$). Let $\Theta$ be a complex Hecke eigensystem over $F$ (a nonzero level ideal together with families $a,b$ indexed by the finite places), and assume the trivial property occurs archimedeanly in the class of $\Theta$ on $D$, i.e. some eigensystem $\Theta'$ agreeing with $\Theta$ away from finitely many places admits a genuine smooth cusp realization at the production pins built from $D$ (level-one subgroups intersected with the finite adelic subgroup, the Hecke generators, the adelic box) for the raw central rescaling of $\Theta'$, in which $b$ is divided by `cNorm`. Fix a real place $w$ of $F$. Then there exist a type $M$ with the structure of a complex vector space, a family of subspaces $\mathrm{wt}:\mathbb{Z}\to\mathrm{Submodule}\,\mathbb{C}\,M$ and three $\mathbb{C}$-linear endomorphisms $E,L,\varepsilon$ of $M$ such that: `IsGL2RealKTypeModule wt E L ε` holds, i.e. $M$ is the internal direct sum of the $\mathrm{wt}(n)$, $E$ maps $\mathrm{wt}(n)$ into $\mathrm{wt}(n+2)$, $L$ maps $\mathrm{wt}(n)$ into $\mathrm{wt}(n-2)$, $E(Lv)-L(Ev)=n\,v$ for $v\in\mathrm{wt}(n)$, $\varepsilon$ maps $\mathrm{wt}(n)$ into $\mathrm{wt}(-n)$, $\varepsilon^2=\mathrm{id}$ and $\varepsilon\circ E=L\circ\varepsilon$; every $\mathrm{wt}(n)$ is finite-dimensional; the module is irreducible in the sense of `IsIrreducibleGL2RealKTypeModule` ($M$ contains a nonzero vector and every submodule compatible with $\mathrm{wt},E,L,\varepsilon$ is $\bot$ or $\top$); the set of $n$ with $\mathrm{wt}(n)\neq\bot$ is infinite; for every $n\in\mathbb{Z}$, the property `HasArchCharacterAt₀` at $w$ for the weight-$n$ character `archWeightCharℝ n` transported along the isomorphism of $F_w$ with $\mathbb{R}$ occurs in the class of $\Theta$ on $D$ (in the above sense) if and only if $\mathrm{wt}(n)\neq\bot$; and for every $k\in\mathbb{Z}$, the conjunction of that weight-$k$ property with `IsArchLoweringAnnihilatedAt w hw` — for all $g$ and all $z$ in the upper half-plane, the archimedean slice $m\mapsto\varphi\bigl(g\,\iota_w(m)\bigr)$ (set to $0$ at singular $m$) is real-differentiable at $\begin{pmatrix}\mathrm{Im}\,z&\mathrm{Re}\,z\\0&1\end{pmatrix}$ and the lowering operator $\tfrac12\bigl(Df(m)[m\,\mathrm{diag}(1,-1)]-i\,Df(m)[m\,\mathrm{antidiag}(1,1)]\bigr)$ vanishes there — occurs in the class of $\Theta$ on $D$ if and only if there is a nonzero $v\in\mathrm{wt}(k)$ with $Lv=0$.
--
--   This is the archimedean classification step at a real place: the weights occurring in the near-equivalence class of $\Theta$ on the covering window $D$, and those weights admitting a vector annihilated by the lowering operator, are exactly the $K$-types and the lowering-annihilated lines of a single irreducible admissible $(\mathfrak{g},K)$-module of $\mathrm{GL}_2(\mathbb{R})$ with finite-dimensional $K$-isotypic pieces and infinite $K$-support. It is used by [`AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_of_coversModCentre`](thm.html#AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_of_coversModCentre), and is assembled from the occurrence of some weight, the parity of differences of occurring weights, stability under $n\mapsto -n$ and $n\mapsto n+2$, the bound $1\le k$ for lowering-annihilated weights, and the two explicit irreducible $K$-type modules (discrete-series-type and parity-type).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchLoweringAnnihilated
import Definitions.Def_AutomorphicForm_GL2RealKTypeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm

theorem AutomorphicForm.exists_isGL2RealKTypeModule_archOccursInClassOf_iff_isArchLoweringAnnihilatedAt_of_coversModCentre
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
              IsArchLoweringAnnihilatedAt w hw φ) ↔
          ∃ v ∈ wt k, v ≠ 0 ∧ L v = 0) := by sorry
