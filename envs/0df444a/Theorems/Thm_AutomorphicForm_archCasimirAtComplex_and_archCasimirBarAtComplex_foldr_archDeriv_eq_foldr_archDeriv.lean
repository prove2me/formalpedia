-- Prove2me | Theorems.Thm_AutomorphicForm_archCasimirAtComplex_and_archCasimirBarAtComplex_foldr_archDeriv_eq_foldr_archDeriv
-- name    : AutomorphicForm.archCasimirAtComplex_and_archCasimirBarAtComplex_foldr_archDeriv_eq_foldr_archDeriv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/5e0f59c2-078a-5f17-b268-176f4ae756ea
-- title:
--   Complex-place Casimir operators commute with archimedean derivative words
-- statement:
--   Let $K$ be a number field, let $m$ be a natural number and let $b$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_K)$, realised as `AdelicGL2 (𝓞 K) K`. Words are finite lists of letters, a letter being either a triple consisting of an infinite place $w$, a proof that $w$ is real and a direction $d \in \{H, E, F\}$, or a triple consisting of an infinite place $w$, a proof that $w$ is complex and a direction in the six-element type $\{H, E, F, iH, iE, iF\}$; the operator $W$ attached to a word is the right fold that applies, for a real letter, $\mathrm{archDerivAt}$ — the function $g \mapsto \frac{d}{dt}\varphi(g\cdot \mathrm{archFlowAt}\,d\,t)|_{t=0}$ for the one-parameter flow in direction $d$ embedded at $w$ — and, for a complex letter, the corresponding $\mathrm{archDerivAtComplex}$, so that the leftmost letter of the word is applied outermost. The hypothesis is that for every word $l$ of length at most $m+2$ the function $W\,l\,b$ is continuous, and is smooth at every infinite place in the sense that for each real place $w$ and each $g$ the map $e \mapsto (W\,l\,b)(g \cdot \mathrm{archRealLiftAt}\,e)$ is $C^\infty$ over $\mathbb{R}$ on the set of real $2\times 2$ matrices of nonzero determinant, and for each complex place $w$ and each $g$ the map $e \mapsto (W\,l\,b)(g\cdot \mathrm{archComplexLiftAt}\,e)$ is $C^\infty$ over $\mathbb{R}$ on the set of complex $2\times 2$ matrices of nonzero determinant. The conclusion is that for every complex place $w$ and every word $l$ of length at most $m$, both $\Omega_w = -\bigl(\tfrac14\partial_H\partial_H - \tfrac12\partial_H + \partial_E\partial_F\bigr)$ and $\bar\Omega_w = -\bigl(\tfrac14\bar\partial_H\bar\partial_H - \tfrac12\bar\partial_H + \bar\partial_E\bar\partial_F\bigr)$, formed from $\partial_X = \tfrac12(X - i\,(iX))$ and $\bar\partial_X = \tfrac12(X + i\,(iX))$ in the complex-place derivations, commute with $W\,l$: $\Omega_w(W\,l\,b) = W\,l\,(\Omega_w b)$ and $\bar\Omega_w(W\,l\,b) = W\,l\,(\bar\Omega_w b)$.
--
--   This is the centrality of the two Casimir elements attached to a complex place, in the form needed for the word calculus: $\Omega_w$ and $\bar\Omega_w$ generate the centre of the universal enveloping algebra of $\mathfrak{sl}_2(\mathbb{C})$ viewed as a real Lie algebra, and hence commute with all invariant derivations, including letters at other infinite places. It is used in the $L^2$ elliptic estimate for archimedean derivative words of Casimir eigenfunctions on the adelic group, and is the complex-place counterpart of the corresponding statement at a real place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_archCasimirAtComplex_and_archCasimirBarAtComplex_foldr_archDeriv_eq_foldr_archDeriv.lean

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

theorem AutomorphicForm.archCasimirAtComplex_and_archCasimirBarAtComplex_foldr_archDeriv_eq_foldr_archDeriv
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
    ∀ (w : InfinitePlace K) (hw : w.IsComplex)
      (l : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
        (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex))), l.length ≤ m →
      archCasimirAtComplex hw (W l b) = W l (archCasimirAtComplex hw b) ∧
        archCasimirBarAtComplex hw (W l b) = W l (archCasimirBarAtComplex hw b) := by sorry
