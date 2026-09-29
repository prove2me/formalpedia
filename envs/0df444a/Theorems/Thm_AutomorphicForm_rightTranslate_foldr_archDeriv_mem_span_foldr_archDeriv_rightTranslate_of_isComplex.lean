-- Prove2me | Theorems.Thm_AutomorphicForm_rightTranslate_foldr_archDeriv_mem_span_foldr_archDeriv_rightTranslate_of_isComplex
-- name    : AutomorphicForm.rightTranslate_foldr_archDeriv_mem_span_foldr_archDeriv_rightTranslate_of_isComplex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/dbf09f24-201e-5f55-ae1a-08dbee08a3bf
-- title:
--   Translates of derivative words lie in spans of equal-length words
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be real numbers, let $j$ be a natural number, and let $\psi$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_K)$ (the units of $2\times 2$ matrices over the adele ring of $K$) that is invariant under left multiplication by the image of $\mathrm{GL}_2(K)$ under `globalPoints`, i.e. $\psi(\gamma g)=\psi(g)$ for all $\gamma\in \mathrm{GL}_2(K)$ and all adelic $g$. A letter is either a real infinite place $v$ of $K$ together with a proof that $v$ is real and a direction in $\{H,E,F^-\}$, or a complex place $v$ with a proof that it is complex and one of the six directions $H,E,F^-,iH,iE,iF^-$; for a list $l$ of letters, $W\,l\,b$ denotes the iterated directional derivative obtained by folding $l$ from the right over $b$, each letter acting by `archDerivAt` respectively `archDerivAtComplex`, that is by $\varphi\mapsto\bigl(g\mapsto \frac{d}{dt}\varphi(g\cdot \text{(flow at that place and direction)}(t))\big|_{t=0}\bigr)$. Assume that for every list $l$ with $\mathrm{length}(l)\le j$ the function $W\,l\,\psi$ is continuous, is smooth at every real place and at every complex place in the sense of `IsArchSmoothAt` and `IsArchSmoothAtComplex` (the matrix-chart maps $e\mapsto (W\,l\,\psi)(g\cdot\text{lift}(e))$ are $C^\infty$ on the locus $\det e\neq 0$, for every $g$), and is bounded on the slab of $g$ whose idele norm of $\det g$, defined through the module character of the adele ring, lies in $[\alpha,\beta]$. The conclusion: for every complex place $w$, every $k$ in the subgroup `rowIsometrySubgroup₀` of the general linear group over the completion $K_w$, and every list $l$ with $\mathrm{length}(l)\le j$, the right translate of $W\,l\,\psi$ by the adelic element `rowIsometryInclAt₀ K w k` (given by $x\mapsto (W\,l\,\psi)(x\cdot \text{that element})$) belongs to the $\mathbb{C}$-span of the functions $W\,l'\,$ applied to the translate of $\psi$ by the same element, as $l'$ ranges over lists of letters with $\mathrm{length}(l')=\mathrm{length}(l)$.
--
--   This is the adjoint-action step for words of invariant derivatives at a complex place: right translation by an element of the maximal compact at $w$ carries a derivative word into a linear combination of words of the same length in the translated function, because $\mathrm{Ad}(k)$ acts linearly on the six real directions of $\mathfrak{sl}_2(\mathbb{C})$ at $w$ and letters at other places commute with the translation. It is used in the $L^p$ estimate for words of complex archimedean derivatives on the archimedean cut submodule, which needs uniform control of derivative words under the compact group at $w$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightTranslate_foldr_archDeriv_mem_span_foldr_archDeriv_rightTranslate_of_isComplex.lean

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

theorem AutomorphicForm.rightTranslate_foldr_archDeriv_mem_span_foldr_archDeriv_rightTranslate_of_isComplex
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
    ∀ (w : InfinitePlace K) (hw : w.IsComplex) (k : rowIsometrySubgroup₀ w.Completion)
      (l : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
        (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex))), l.length ≤ j →
      rightTranslate K (rowIsometryInclAt₀ K w k) (W l ψ) ∈
        Submodule.span ℂ (Set.range fun l' : {l' : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
            (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) // l'.length = l.length} =>
          W l'.1 (rightTranslate K (rowIsometryInclAt₀ K w k) ψ)) := by sorry
