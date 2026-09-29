-- Prove2me | Theorems.Thm_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt
-- name    : AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/c8508f0a-7a83-5ddd-a211-23f6a8a3e3ba
-- title:
--   Regularity and slab bounds inherited by row-isometry translates
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta\in\mathbb{R}$, let $j\in\mathbb{N}$, and let $\psi\colon GL_2(\mathbb{A}_K)\to\mathbb{C}$ be a function on the adelic group $GL_2$ of the adele ring of $K$ that is left invariant under the global points, i.e. $\psi(\gamma g)=\psi(g)$ for all $\gamma\in GL_2(K)$ (embedded via `globalPoints`) and all $g$. For a list $l$ of letters, each letter being either a real place $v$ together with a proof that $v$ is real and a direction $d\in\{H,E,F^-\}$, or a complex place $v$ together with a proof that $v$ is complex and one of the six directions of `ArchDirComplex`, let $W\,l$ be the operator obtained by folding the list from the right, applying at a real letter the derivation $\varphi\mapsto\big(g\mapsto \tfrac{d}{dt}\varphi(g\cdot\text{archFlow}_{v,d}(t))|_{t=0}\big)$ and at a complex letter the corresponding derivation along the complex archimedean flow, so that the leftmost letter acts outermost. Assume that for every $l$ with $\mathrm{length}(l)\le j$ the function $W\,l\,\psi$ is continuous, is $C^\infty$ along the real archimedean directions at every real place and along the complex archimedean directions at every complex place (in the sense of `IsArchSmoothAt` and `IsArchSmoothAtComplex`, smoothness of $e\mapsto \varphi(g\cdot\text{lift}(e))$ on the locus of invertible matrices), and is bounded on the slab where the idele norm of $\det g$, defined by the distributive Haar character, lies in $[\alpha,\beta]$. Then for every real place $w$ of $K$, every witness that $w$ is real, and every $k$ in the group `rowIsometrySubgroup₀ w.Completion`, the right translate $g\mapsto\psi\big(g\cdot \text{rowIsometryInclAt₀}\,K\,w\,k\big)$ is again left $GL_2(K)$-invariant, and for every list $l$ with $\mathrm{length}(l)\le j$ the function $W\,l$ applied to this translate is continuous, satisfies the smoothness conditions at every real and every complex place, and is bounded on the same slab $\alpha\le\|\det g\|\le\beta$.
--
--   This is the statement that the class of left $GL_2(K)$-invariant functions all of whose archimedean derivative words of length at most $j$ are continuous, smooth at the infinite places and bounded on a determinant slab is stable under right translation by the row-isometry group at a real place; the mechanism is that letters at other places commute with the translation while a letter at $w$ becomes, after conjugation, a fixed real combination of $H$, $E$ and $F^-$. It is used in the construction of the archimedean cut-off and $L^p$ estimates, being cited by [`AutomorphicForm.exists_forall_eLpNorm_archDerivAt_E_sub_Fm_foldr_le_of_mem_archCutSubmodule`](thm.html#AutomorphicForm.exists_forall_eLpNorm_archDerivAt_E_sub_Fm_foldr_le_of_mem_archCutSubmodule).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt.lean

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
open AutomorphicForm
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.forall_continuous_isArchSmoothAt_bounded_foldr_archDeriv_rightTranslate_rowIsometryInclAt
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
    ∀ (w : InfinitePlace K) (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion),
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
