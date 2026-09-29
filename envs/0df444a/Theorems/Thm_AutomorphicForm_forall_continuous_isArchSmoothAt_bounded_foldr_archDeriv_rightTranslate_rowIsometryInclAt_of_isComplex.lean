-- Prove2me | Theorems.Thm_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt_of_isComplex
-- name    : AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/aae562e9-87bc-5894-882b-fee0b599b710
-- title:
--   Regularity inherited by row-isometry translates at a complex place
-- statement:
--   Let $K$ be a number field, $\alpha,\beta$ real numbers, $j$ a natural number, and $\psi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ a function that is left invariant under the image of $\mathrm{GL}_2(K)$ under `globalPoints`, i.e. $\psi(\gamma g)=\psi(g)$ for all $\gamma\in\mathrm{GL}_2(K)$ and all adelic $g$. Write $W$ for the operator attached to a list of letters, each letter being either a real place $v$ together with a proof that $v$ is real and a direction in $\{H,E,F\}$, or a complex place $v$ together with a proof that $v$ is complex and one of the six directions $H,E,F,iH,iE,iF$; $W$ applies, from the right end of the list inwards, the corresponding one-parameter flow derivative $\varphi\mapsto\bigl(g\mapsto \frac{d}{dt}\varphi(g\cdot\mathrm{flow}(t))|_{t=0}\bigr)$, namely `archDerivAt` at real letters and `archDerivAtComplex` at complex letters. Assume that for every list $l$ of length at most $j$ the function $W\,l\,\psi$ is continuous, satisfies `IsArchSmoothAt` at every real place and `IsArchSmoothAtComplex` at every complex place (i.e. is $C^\infty$ in the $2\times2$ matrix entries of the archimedean coordinate at that place, on the locus of nonvanishing determinant, after translation by any $g$), and is bounded on the slab where the idele norm of $\det g$ lies in $[\alpha,\beta]$. The conclusion is that for every complex place $w$ of $K$ and every $k$ in the row-isometry subgroup `rowIsometrySubgroup₀` of $\mathrm{GL}_2(K_w)$, the right translate $\psi(\cdot\, \iota_w(k))$ by the adelic image `rowIsometryInclAt₀` of $k$ is again left $\mathrm{GL}_2(K)$-invariant, and for every list $l$ of length at most $j$ the function $W\,l$ applied to this translate is continuous, is `IsArchSmoothAt` at every real place, is `IsArchSmoothAtComplex` at every complex place, and is bounded on the same slab.
--
--   This is the stability of the regularity and growth conditions defining an automorphic form under right translation by the maximal compact (row-isometry) subgroup at a complex place, the complex-place counterpart of the corresponding statement at real places; the mechanism is that a real direction $X$ of $\mathfrak{sl}_2(\mathbb{C})$ satisfies $X R_k = R_k \mathrm{Ad}(k^{-1})X$, with $\mathrm{Ad}(k^{-1})X$ a fixed real combination of the six directions. It is used in establishing $L^p$ bounds for words of archimedean derivatives and in the description of right translates of derivative words as lying in the span of derivative words of translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt_of_isComplex.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt_of_isComplex
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (j : ℕ)
    (ψ : AdelicGL2 (𝓞 K) K → ℂ)
    (hinv : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), ψ (globalPoints (𝓞 K) K γ * g) = ψ g) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    (∀ l, l.length ≤ j →
      Continuous (W l ψ) ∧
      (∀ (v : InfinitePlace K) (hv : v.IsReal), IsArchSmoothAt hv (W l ψ)) ∧
      (∀ (v : InfinitePlace K) (hv : v.IsComplex), IsArchSmoothAtComplex hv (W l ψ)) ∧
      ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
        NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖W l ψ g‖ ≤ B) →
    ∀ (w : InfinitePlace K) (hw : w.IsComplex) (k : rowIsometrySubgroup₀ w.Completion),
      (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        rightTranslate K (rowIsometryInclAt₀ K w k) ψ (globalPoints (𝓞 K) K γ * g) =
          rightTranslate K (rowIsometryInclAt₀ K w k) ψ g) ∧
      ∀ l, l.length ≤ j →
        Continuous (W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ)) ∧
        (∀ (v : InfinitePlace K) (hv : v.IsReal), IsArchSmoothAt hv (W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ))) ∧
        (∀ (v : InfinitePlace K) (hv : v.IsComplex),
          IsArchSmoothAtComplex hv (W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ))) ∧
        ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
          NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β →
            ‖W l (rightTranslate K (rowIsometryInclAt₀ K w k) ψ) g‖ ≤ B := by sorry
