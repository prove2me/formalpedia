-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_archDerivAt_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
-- name    : AutomorphicForm.exists_forall_eLpNorm_archDerivAt_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/bb965c4d-95e7-559c-9a67-832a2ce74f25
-- title:
--   Single-letter L² derivative bound at a real place
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, let `tys` be an `ArchTypeFamily K` (a number $\mathrm{card}\,w$ of archimedean types together with representations $\mathrm{rep}\,w\,i$ at each infinite place $w$), and let $m$ be a natural number. Write $W$ for the word operator: for a list $l$ whose letters are either a real place $w$ with a proof of $w.\mathrm{IsReal}$ and a direction $d\in\{H,E,F^-\}$, or a complex place with a proof of $w.\mathrm{IsComplex}$ and a direction in `ArchDirComplex`, $W\,l\,b$ is the right fold of the corresponding one-parameter derivations $\varphi\mapsto(g\mapsto \tfrac{d}{dt}\varphi(g\cdot \mathrm{flow}(t))|_{t=0})$, namely `archDerivAt` respectively `archDerivAtComplex`, applied to $b$. The assertion: there exists $c\ge 0$ such that for every $\Lambda\ge 1$ and every $b:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfying (i) $b(\gamma g)=b(g)$ for all $\gamma\in \mathrm{GL}_2(K)$ embedded by `globalPoints` and all $g$; (ii) $b\in$ `archCutSubmodule K tys`, the infimum over infinite places $w$ of the supremum over $i<\mathrm{card}\,w$ of the type submodules `archTypeSubmoduleAt K w (tys.rep w i)`; (iii) for every word $l$ of length $\le m+2$, $W\,l\,b$ is continuous, is `IsArchSmoothAt` at every real place and `IsArchSmoothAtComplex` at every complex place (infinite differentiability in the matrix-entry charts at that place), and is bounded on the slab $\{g: \|\det g\|_{\mathbb{A}}\in[\alpha,\beta]\}$ for the idele norm; then for every real place $w$, if there is $\lambda\in\mathbb{C}$ with $|\lambda|\le\Lambda$ and `archCasimirAt` $b=\lambda\, b$ (the Casimir at $w$ being $-(\tfrac14 H^2-\tfrac12 H+EF^-)$), then for every single letter $d\in\{H,E,F^-\}$ at $w$ and every word $l$ with $|l|+1\le m$, $$\|\,\mathrm{archDerivAt}\,d\,(W\,l\,b)\,\|_{L^2} \le c\sqrt{\Lambda}\;\|W\,l\,b\|_{L^2},$$ the $L^2$ norms being `eLpNorm` with exponent $2$ for the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ restricted to `canonicalTruncationDomain K α β`, and the constant on the right being $\mathrm{ENNReal.ofReal}(c\sqrt{\Lambda})$. Note that the eigenvalue hypothesis is imposed on $b$ itself, while the conclusion concerns all derivative words $W\,l\,b$ of length at most $m-1$.
--
--   This is the induction step of the $L^2$ elliptic (Gårding-type) estimate for $K$-finite Casimir eigenfunctions on a truncated fundamental domain: a single further derivative in any $\mathfrak{sl}_2$ direction at a real place costs at most $\sqrt{\Lambda}$ in $L^2$. It is used to obtain the bound for words of arbitrary length, in [`AutomorphicForm.exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul`](thm.html#AutomorphicForm.exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_eLpNorm_archDerivAt_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul.lean

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

theorem AutomorphicForm.exists_forall_eLpNorm_archDerivAt_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
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
        ∀ (w : InfinitePlace K) (hw : w.IsReal),
          (∃ lam : ℂ, ‖lam‖ ≤ Λ ∧ archCasimirAt hw b = lam • b) →
          ∀ (d : ArchDir) (l : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
              (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex))), l.length + 1 ≤ m →
            eLpNorm (archDerivAt hw d (W l b)) 2
                ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
              ENNReal.ofReal (c * Real.sqrt Λ) *
                eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
