-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
-- name    : AutomorphicForm.exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/9bcf63e6-f4f2-5ede-bcf6-f1ae3e9218b2
-- title:
--   L² bounds for derivative words of Casimir eigenfunctions
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, let `tys` be an `ArchTypeFamily` for $K$ (for each infinite place $w$ a natural number `card w` together with, for each $i<\mathrm{card}\,w$, a finite-dimensional representation of `rowIsometrySubgroup₀` of $K_w$), and let $m$ be a natural number. For a list $l$ of labels, each label being either a real place $w$ with a direction in $\{H,E,F\}$ or a complex place $w$ with one of the six directions of `ArchDirComplex`, write $W\,l\,b$ for the right-fold of the corresponding invariant derivatives `archDerivAt`/`archDerivAtComplex` applied to $b:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, each such derivative being $g\mapsto \frac{d}{dt}\big|_{t=0}\varphi(g\cdot\text{(flow at }w\text{ in that direction)}(t))$. The assertion is that there exists $c\ge 0$ such that for every $\Lambda\ge 1$ and every $b$ satisfying: $b(\gamma g)=b(g)$ for all $\gamma\in\mathrm{GL}_2(K)$ embedded via `globalPoints` and all $g$; membership of $b$ in `archCutSubmodule K tys`, i.e. for each infinite place $w$, $b$ lies in the supremum over $i$ of the type submodules `archTypeSubmoduleAt` attached to `tys.rep w i`; for every list $l$ of length at most $m+2$, $W\,l\,b$ is continuous, is `IsArchSmoothAt` at every real place and `IsArchSmoothAtComplex` at every complex place, and is bounded on $\{g:\ \text{idele norm of }\det g\in[\alpha,\beta]\}$ (the idele norm being the `distribHaarChar` modulus); at every real place $w$, $\Omega_w b=\lambda b$ with $\|\lambda\|\le\Lambda$, and at every complex place $w$, $\Omega_w b=\lambda b$ and $\bar\Omega_w b=\lambda' b$ with $\|\lambda\|,\|\lambda'\|\le\Lambda$, where $\Omega,\bar\Omega$ are `archCasimirAt`, `archCasimirAtComplex`, `archCasimirBarAtComplex`; then for every list $l$ with $|l|\le m$,
--   $$\|W\,l\,b\|_{L^2}\le c\,\Lambda^{|l|/2}\,\|b\|_{L^2},$$
--   the $L^2$-norms being `eLpNorm` for the adelic $\mathrm{GL}_2$ Haar measure restricted to `canonicalTruncationDomain K α β`, and the scalar appearing as `ENNReal.ofReal (c * Λ ^ (|l| / 2))`.
--
--   This is the $L^2$ elliptic estimate for archimedean derivative words of a $K_\infty$-finite Casimir eigenfunction on a truncated slab $\alpha\le\|\det\|\le\beta$: derivatives of order at most $m$ cost at most $\Lambda^{m/2}$ in the $L^2$ norm, uniformly in the eigenvalue bound $\Lambda$. It feeds the sup-norm bound for elements of an isotypic cusp space with bounded Casimir eigenvalues, via a Sobolev-type argument on the truncation domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul.lean

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
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (tys : ArchTypeFamily K) (m : ℕ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (Λ : ℝ), 1 ≤ Λ →
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), b (globalPoints (𝓞 K) K γ * g) = b g) →
        b ∈ archCutSubmodule K tys →

        (∀ l, l.length ≤ m + 2 →
          Continuous (W l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b)) ∧
          ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
            NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β → ‖W l b g‖ ≤ B) →

        (∀ (w : InfinitePlace K) (hw : w.IsReal), ∃ lam : ℂ, ‖lam‖ ≤ Λ ∧ archCasimirAt hw b = lam • b) →
        (∀ (w : InfinitePlace K) (hw : w.IsComplex), ∃ lam lam' : ℂ, ‖lam‖ ≤ Λ ∧ ‖lam'‖ ≤ Λ ∧
          archCasimirAtComplex hw b = lam • b ∧ archCasimirBarAtComplex hw b = lam' • b) →
        ∀ l, l.length ≤ m →
          eLpNorm (W l b) 2
              ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
            ENNReal.ofReal (c * Λ ^ ((l.length : ℝ) / 2)) *
              eLpNorm b 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
