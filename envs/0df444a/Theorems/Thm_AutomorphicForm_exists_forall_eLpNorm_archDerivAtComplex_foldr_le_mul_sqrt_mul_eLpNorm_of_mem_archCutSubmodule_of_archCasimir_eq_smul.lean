-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
-- name    : AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/f3941cf6-ad4d-592f-9f9b-b6221f30cb90
-- title:
--   Single-letter L² bound at a complex place for Casimir eigenfunctions
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, let `tys` be an archimedean type family on $K$ (data of a number $\mathrm{card}\,w$ for each infinite place $w$ together with representations $\mathrm{rep}\,w\,i$, $i<\mathrm{card}\,w$), and let $m$ be a natural number. For a list $l$ of letters, each letter being either a real place $w$ with a direction in $\{H,E,F^-\}$ or a complex place $w$ with a direction among the six elements of `ArchDirComplex`, write $W\,l\,b$ for the right fold applying the corresponding operators `archDerivAt` resp. `archDerivAtComplex` to $b$ (each such operator differentiates along the relevant one-parameter flow at the place, at the parameter value $0$). The assertion is the existence of a constant $c\ge 0$ such that for every $\Lambda\ge 1$ and every function $b:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ satisfying: $b(\iota(\gamma)g)=b(g)$ for all $\gamma\in \mathrm{GL}_2(K)$ and all $g$, where $\iota$ is the map `globalPoints` induced by $K\to\mathbb A_K$; $b$ lies in `archCutSubmodule K tys`, the infimum over infinite places $w$ of the supremum over $i<\mathrm{card}\,w$ of the type submodules $\mathrm{archTypeSubmoduleAt}$ attached to $\mathrm{rep}\,w\,i$; and every word $l$ with $|l|\le m+2$ has $W\,l\,b$ continuous, smooth in the archimedean sense at every real place and at every complex place (that is, $e\mapsto (W\,l\,b)(g\cdot \text{lift}(e))$ is $C^\infty$ on the invertible matrices for each $g$), and bounded on the slab $\{g:\ \mathrm{ideleNorm}_K(\det g)\in[\alpha,\beta]\}$; then for every complex place $w$ of $K$ for which there are $\lambda,\lambda'\in\mathbb C$ with $\|\lambda\|\le\Lambda$, $\|\lambda'\|\le\Lambda$, $\Omega_w b=\lambda b$ and $\bar\Omega_w b=\lambda' b$ (with $\Omega_w=$ `archCasimirAtComplex`, $\bar\Omega_w=$ `archCasimirBarAtComplex`, the second-order expressions $-\bigl(\tfrac14\partial_H^2-\tfrac12\partial_H+\partial_E\partial_{F^-}\bigr)$ in the holomorphic resp. antiholomorphic directions at $w$), every direction $d$ and every word $l$ with $|l|+1\le m$ satisfy $$\|\partial_{w,d}(W\,l\,b)\|_{L^2} \le c\sqrt{\Lambda}\,\|W\,l\,b\|_{L^2},$$ the $L^2$ norms being `eLpNorm` at exponent $2$ for the adelic Haar measure on $\mathrm{GL}_2(\mathbb A_K)$ restricted to `canonicalTruncationDomain K α β`, and the right-hand factor being $\mathrm{ENNReal.ofReal}(c\sqrt\Lambda)$.
--
--   This is the single-letter step of the $L^2$ elliptic estimate at a complex place: one further derivative of a derivative word of a Casimir eigenfunction costs at most $c\sqrt{\Lambda}$ in $L^2$ over the canonical truncation domain of the norm slab $[\alpha,\beta]$. It is used in the induction that bounds whole derivative words, [`AutomorphicForm.exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul`](thm.html#AutomorphicForm.exists_forall_eLpNorm_foldr_archDeriv_le_mul_rpow_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul.lean

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

theorem AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul
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
        ∀ (w : InfinitePlace K) (hw : w.IsComplex),
          (∃ lam lam' : ℂ, ‖lam‖ ≤ Λ ∧ ‖lam'‖ ≤ Λ ∧
            archCasimirAtComplex hw b = lam • b ∧ archCasimirBarAtComplex hw b = lam' • b) →
          ∀ (d : ArchDirComplex) (l : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
              (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex))), l.length + 1 ≤ m →
            eLpNorm (archDerivAtComplex hw d (W l b)) 2
                ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
              ENNReal.ofReal (c * Real.sqrt Λ) *
                eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
