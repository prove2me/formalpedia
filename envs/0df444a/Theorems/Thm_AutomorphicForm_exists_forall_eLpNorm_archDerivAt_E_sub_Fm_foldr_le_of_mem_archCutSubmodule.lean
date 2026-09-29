-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_archDerivAt_E_sub_Fm_foldr_le_of_mem_archCutSubmodule
-- name    : AutomorphicForm.exists_forall_eLpNorm_archDerivAt_E_sub_Fm_foldr_le_of_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/47abf109-7598-5115-87af-329eb8d21f6f
-- title:
--   Weight bound for E-F on archimedean derivative words
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, let `tys` be an `ArchTypeFamily` for $K$ (for each infinite place $w$ a cardinality `card w` together with representations `rep w i : ArchRepAt K w`, $i <$ `card w`), and let $m$ be a natural number. Write $W$ for the word operator which, given a list $l$ of letters, each letter being either a triple $(w,\,hw : w$ real$,\,d :$ `ArchDir`$)$ or a triple $(w,\,hw : w$ complex$,\,d :$ `ArchDirComplex`$)$, sends a function $b$ on $\mathrm{GL}_2$ of the adeles of $K$ to the right fold of $l$ applying at each letter the corresponding one-parameter derivative `archDerivAt hw d` (the derivative at $t=0$ of $g \mapsto \varphi(g\cdot$ `archFlowAt hw d t`$)$) or `archDerivAtComplex hw d`. The assertion is that there exists $n_0 \in \mathbb{N}$ such that for every $b : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfying: (i) $b(\gamma g) = b(g)$ for all $\gamma \in \mathrm{GL}_2(K)$ (embedded by `globalPoints`) and all $g$; (ii) $b$ lies in `archCutSubmodule K tys`, the infimum over infinite places $w$ of the span of the submodules `archTypeSubmoduleAt K w (tys.rep w i)`; (iii) for every word $l$ of length $\le m+2$, $W\,l\,b$ is continuous, is `IsArchSmoothAt` at every real place and `IsArchSmoothAtComplex` at every complex place (i.e. $e \mapsto (W\,l\,b)(g\cdot$ `archRealLiftAt hw e`$)$, resp. the complex analogue, is $C^\infty$ on the locus of invertible matrices, for every $g$), and is bounded on the slab $\{g :$ `ideleNorm K (det g)` $\in [\alpha,\beta]\}$, where the idele norm is the modulus of `distribHaarChar`; then for every real place $w$ of $K$ and every word $l$ of length $\le m$, $$\bigl\| \mathrm{archDerivAt}_{w,E}(W\,l\,b) - \mathrm{archDerivAt}_{w,F^-}(W\,l\,b)\bigr\|_{L^2} \le (n_0 + 2\,|l|)\,\bigl\| W\,l\,b \bigr\|_{L^2},$$ both $L^2$-norms being `eLpNorm` with exponent $2$ for the adelic Haar measure `adelicGLHaar` on $\mathrm{GL}_2$ restricted to `canonicalTruncationDomain K α β`, and the constant being the cast of the natural number $n_0 + 2\,|l|$ to $\mathbb{E}\mathbb{N}\mathbb{R}$-valued reals.
--
--   This is the $K$-type control statement at a real place: a function cut out by a finite family of archimedean types has $SO(2)_w$-weights confined to a window $[-n_0,n_0]$, each archimedean letter shifts the weight at $w$ by at most $2$, and on the weight space of weight $n$ the operator $E - F^-$ acts by $in$, whence the bound with constant $n_0 + 2|l|$ for words of length $|l|$. It feeds the Casimir-based $L^2$ estimate for derivative words of arch-cut functions on the canonical truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_eLpNorm_archDerivAt_E_sub_Fm_foldr_le_of_mem_archCutSubmodule.lean

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

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_eLpNorm_archDerivAt_E_sub_Fm_foldr_le_of_mem_archCutSubmodule
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (tys : ArchTypeFamily K) (m : ℕ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    ∃ n₀ : ℕ,
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), b (globalPoints (𝓞 K) K γ * g) = b g) →
        b ∈ archCutSubmodule K tys →
        (∀ l, l.length ≤ m + 2 →
          Continuous (W l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b)) ∧
          ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖W l b g‖ ≤ B) →
        ∀ (w : InfinitePlace K) (hw : w.IsReal) (l : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
              (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex))), l.length ≤ m →
          eLpNorm (archDerivAt hw .E (W l b) - archDerivAt hw .Fm (W l b)) 2
              ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
            ((n₀ + 2 * l.length : ℕ) : ENNReal) *
              eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
