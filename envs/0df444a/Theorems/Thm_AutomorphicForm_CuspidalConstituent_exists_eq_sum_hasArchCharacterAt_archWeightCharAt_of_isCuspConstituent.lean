-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/1da62bbb-e440-52d7-a406-bc3a0bd2ce1b
-- title:
--   Weight decomposition of cut vectors at real places
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $K$. Put $D=\bigcup_{x\in T}Dx$, where $D$ is the centre-cut Siegel set `centreCutSiegelSet K c u d₁ d₂` of those $g$ whose finite part lies in `finiteIntegralGL2` and whose archimedean parts satisfy $c\le$ `localHeight`, `xWindowSq` $\le u^2$ and `archDetNorm` $\in[d_1,d_2]$ at every infinite place; assume `CoversModCentre K` for this union, i.e. every $g$ admits $\gamma\in \mathrm{GL}_2(K)$ and a central adelic scalar $z$ with $\gamma g z$ in the union. Let `pins` be the carrier data `productionPinsOf` attached to this union, with level groups $N\mapsto$ `levelOne` $\sqcap$ `finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`, full central group $\top$ and the measure conditioned on `adelicBox`; let $\xi$ be a character of that central group, $N\ne 0$ an ideal of $\mathcal O_K$, and `tys` a family assigning to each infinite place finitely many archimedean types. Assume $V$ is a cuspidal constituent for these data, i.e. `IsCuspSubrep` holds for $V$ with character $\xi$, $V\ne 0$, and every cusp subrepresentation contained in $V$ is $0$ or $V$. Let $y$ lie in $V$, be invariant under right translation by `levelOne` $N$ $\sqcap$ `finiteAdelicGL2Subgroup`, and lie in `archCutSubmodule K tys`, the intersection over infinite places $w$ of the sum of the type submodules for the types listed at $w$. Then there are $m\in\mathbb N$ and $y_1,\dots,y_m$, each again in $V$, of level $N$ in the above sense and in the archimedean cut, such that $y=\sum_j y_j$ and such that for every $j$ and every real place $w$ there is $n\in\mathbb Z$ with `HasArchCharacterAt₀ K w (archWeightCharAt hw n) (ys j)`, that is, $y_j$ transforms at $w$ by the $n$-th power of the basic weight character `archWeightOneAt hw` on `rowIsometrySubgroup₀` of the completion at $w$.
--
--   This is the decomposition of a level-and-type cut vector in a cuspidal constituent into vectors of pure weight at each real place, the adelic form of the statement that a $K$-finite vector for a compact torus is a finite sum of weight vectors; complex places are untouched. It is used in the analysis of archimedean types of cuspidal constituents, in particular by the lemmas computing the Casimir eigenvalue and separating discrete-series, principal-series and trivial behaviour, and by the construction of non-zero vectors in the type cut.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (tys : AutomorphicForm.ArchTypeFamily K)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) :
    ∃ (m : ℕ) (ys : Fin m → (AdelicGL2 (𝓞 K) K → ℂ)),
      (∀ j, ys j ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys) ∧
      (∀ j, ∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ n : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw n) (ys j)) ∧
      y = ∑ j, ys j := by sorry
