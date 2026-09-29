-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule
-- name    : AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/038840a7-3657-5ab9-ae26-9c3187c5dad3
-- title:
--   SU(2)-type control at a complex place in L²
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, let `tys` be an `ArchTypeFamily` for $K$ (a number `card w` of archimedean types together with a choice `rep w i` of archimedean representation type at each infinite place $w$), and let $m$ be a natural number. Write $W(l)$ for the word operator attached to a list $l$ of letters, each letter being either a real place $w$ with a direction in $\{H,E,F^-\}$ or a complex place $w$ with a direction in $\{H,E,F^-,iH,iE,iF^-\}$, acting by folding the corresponding infinitesimal right translations $\varphi\mapsto\bigl(g\mapsto \tfrac{d}{dt}\varphi(g\cdot \mathrm{flow}_t)\big|_{t=0}\bigr)$ from the right end of the list. The assertion is that there exists $n_0\in\mathbb N$, depending only on $K$, $\alpha$, $\beta$, `tys` and $m$, such that for every $b:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ satisfying: $b(\gamma g)=b(g)$ for all $\gamma\in\mathrm{GL}_2(K)$ (embedded by `globalPoints`) and all $g$; membership of $b$ in `archCutSubmodule K tys`, the intersection over infinite places $w$ of the sum of the type submodules `archTypeSubmoduleAt K w (tys.rep w i)` for $i<$ `tys.card w`; and, for every list $l$ of length at most $m+2$, that $W(l)b$ is continuous, is archimedean smooth at every real place and at every complex place (in the sense that $e\mapsto W(l)b(g\cdot \mathrm{lift}(e))$ is $C^\infty$ on invertible matrices, for each $g$), and is bounded on the slab of $g$ whose idele norm $\lvert\det g\rvert$, defined via the `distribHaarChar` of the adele ring, lies in $[\alpha,\beta]$ — one has, for every complex place $w$ and every list $l$ of length at most $m$, the three inequalities $$\lVert iH_w\,W(l)b\rVert_2,\ \lVert (E_w-F^-_w)W(l)b\rVert_2,\ \lVert (iE_w+iF^-_w)W(l)b\rVert_2\ \le\ (n_0+2\,\mathrm{length}(l))\,\lVert W(l)b\rVert_2,$$ all $L^2$ norms (`eLpNorm` with exponent $2$, valued in $[0,\infty]$) being taken for the adelic Haar measure on $\mathrm{GL}_2(\mathbb A_K)$ restricted to the canonical truncation domain `canonicalTruncationDomain K α β`.
--
--   This is $K$-type control at a complex place: the three directions $iH$, $E-F^-$, $iE+iF^-$ span the compact Lie algebra $\mathfrak{su}(2)$ inside $\mathfrak{sl}_2(\mathbb C)$ at $w$, and the statement bounds their effect on derivative words of a function cut by finitely many archimedean types, with a constant growing linearly in the word length. It feeds the Casimir-type $L^2$ estimate [`AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul`](thm.html#AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule.lean

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
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.CuspidalConstituent
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_eLpNorm_archDerivAtComplex_iH_and_E_sub_Fm_and_iE_add_iFm_foldr_le_of_mem_archCutSubmodule
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
        ∀ (w : InfinitePlace K) (hw : w.IsComplex) (l : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
              (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex))), l.length ≤ m →
          eLpNorm (archDerivAtComplex hw .iH (W l b)) 2
              ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
            ((n₀ + 2 * l.length : ℕ) : ENNReal) *
              eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ∧
          eLpNorm (archDerivAtComplex hw .E (W l b) - archDerivAtComplex hw .Fm (W l b)) 2
              ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
            ((n₀ + 2 * l.length : ℕ) : ENNReal) *
              eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ∧
          eLpNorm (archDerivAtComplex hw .iE (W l b) + archDerivAtComplex hw .iFm (W l b)) 2
              ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤
            ((n₀ + 2 * l.length : ℕ) : ENNReal) *
              eLpNorm (W l b) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
