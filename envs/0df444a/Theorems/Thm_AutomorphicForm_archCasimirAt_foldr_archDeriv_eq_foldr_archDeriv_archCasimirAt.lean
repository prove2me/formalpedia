-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAt_foldr_archDeriv_eq_foldr_archDeriv_archCasimirAt
-- name    : AutomorphicForm.archCasimirAt_foldr_archDeriv_eq_foldr_archDeriv_archCasimirAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/2b447d1a-b5ee-5826-9dc0-61471f6f22d8
-- title:
--   Casimir at a real place commutes with derivation words
-- statement:
--   Let $K$ be a number field, let $m$ be a natural number and let $b$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_K)$, the group `AdelicGL2 (𝓞 K) K` of invertible $2\times 2$ matrices over the adele ring. A letter is either a real place $w$ of $K$ together with a proof that it is real and a direction $d \in \{H, E, F^-\}$, or a complex place together with a proof that it is complex and one of the six directions of `ArchDirComplex`; for a list $l$ of letters, $W\,l\,\varphi$ denotes the right-to-left fold of $l$ over $\varphi$, each real letter acting by `archDerivAt`, i.e. $\varphi \mapsto (g \mapsto \frac{d}{dt}\varphi(g\cdot \mathrm{archFlowAt}\,hw\,d\,t)|_{t=0})$, and each complex letter by the corresponding `archDerivAtComplex`. Assume that for every list $l$ of length at most $m+2$ the function $W\,l\,b$ is continuous and is arch-smooth at every infinite place, meaning that for each $g$ the map sending a real (resp. complex) $2\times 2$ matrix $e$ of nonzero determinant to $(W\,l\,b)(g\cdot \mathrm{archRealLiftAt}\,hw\,e)$ (resp. $g\cdot \mathrm{archComplexLiftAt}\,hw\,e$) is $C^\infty$ over $\mathbb{R}$ on that set. Then for every real place $w$ and every list $l$ of length at most $m$, $\mathrm{archCasimirAt}\,hw\,(W\,l\,b) = W\,l\,(\mathrm{archCasimirAt}\,hw\,b)$, where $\mathrm{archCasimirAt}\,hw\,\varphi = -\bigl(\tfrac14 H_wH_w\varphi - \tfrac12 H_w\varphi + E_wF^-_w\varphi\bigr)$.
--
--   This is the centrality of the Casimir element of $U(\mathfrak{sl}_2)$, transcribed into the alphabet of invariant derivations at the infinite places used in the adelic setting: the Casimir operator at a real place commutes with arbitrary words of length at most $m$ in the derivations at all infinite places, for functions whose words of length up to $m+2$ are continuous and arch-smooth. It feeds the $L^2$ elliptic estimate for Casimir eigenfunctions in [`AutomorphicForm.exists_forall_eLpNorm_archDerivAt_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul`](thm.html#AutomorphicForm.exists_forall_eLpNorm_archDerivAt_foldr_le_mul_sqrt_mul_eLpNorm_of_mem_archCutSubmodule_of_archCasimir_eq_smul), the commutation at the place $w$ coming from the $\mathfrak{sl}_2$ relations and the commutation across distinct places from the symmetry of mixed derivatives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAt_foldr_archDeriv_eq_foldr_archDeriv_archCasimirAt.lean

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

theorem AutomorphicForm.archCasimirAt_foldr_archDeriv_eq_foldr_archDeriv_archCasimirAt
    (K : Type) [Field K] [NumberField K] (m : ℕ)
    (b : AdelicGL2 (𝓞 K) K → ℂ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    (∀ l, l.length ≤ m + 2 →
      Continuous (W l b) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b))) →
    ∀ (w : InfinitePlace K) (hw : w.IsReal)
      (l : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
        (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex))), l.length ≤ m →
      archCasimirAt hw (W l b) = W l (archCasimirAt hw b) := by sorry
