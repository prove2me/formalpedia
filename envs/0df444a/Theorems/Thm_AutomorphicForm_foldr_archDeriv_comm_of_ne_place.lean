-- Prove2me | Theorems.Thm_AutomorphicForm_foldr_archDeriv_comm_of_ne_place
-- name    : AutomorphicForm.foldr_archDeriv_comm_of_ne_place
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/0939b2dc-05a2-5968-b3bd-6d75a543765e
-- title:
--   Archimedean derivations at distinct infinite places commute
-- statement:
--   Let $K$ be a number field and let $\varphi$ be a complex-valued function on $\mathrm{GL}_2(\mathbb{A}_K)$, the group `AdelicGL2 (𝓞 K) K` of invertible $2\times 2$ matrices over the adele ring. A direction datum is either a triple consisting of an infinite place $w$, a proof that $w$ is real and an element $d$ of `ArchDir` (one of $H$, $E$, $F$), or a triple consisting of an infinite place $w$, a proof that $w$ is complex and an element of `ArchDirComplex` (one of $H, E, F, iH, iE, iF$). For a list $l$ of such data, $W\,l$ denotes the operator on functions obtained by right-folding the corresponding one-place derivations: a real datum acts by `archDerivAt`, sending $\psi$ to $g \mapsto \frac{d}{dt}\psi(g\cdot \mathrm{archFlowAt}(d,t))|_{t=0}$ along the one-parameter subgroup embedded at $w$, and a complex datum acts by `archDerivAtComplex` in the same way; thus $W\,[d,d']\,\varphi$ is the $d$-derivative of the $d'$-derivative of $\varphi$. Assume that for every list $l$ of length at most $2$ the function $W\,l\,\varphi$ is continuous, and that it is archimedean-smooth at every infinite place, meaning that for each real place $w$ and each $g$ the map $e \mapsto (W\,l\,\varphi)(g\cdot \mathrm{archRealLiftAt}(e))$ is $C^\infty$ on the real $2\times 2$ matrices of nonzero determinant, and correspondingly for each complex place with the complex lift and real smoothness. Then for any two direction data $d$, $d'$ whose underlying infinite places are distinct, $W\,[d,d']\,\varphi = W\,[d',d]\,\varphi$.
--
--   This is the symmetry-of-second-derivatives (Clairaut–Schwarz) statement for the right-invariant archimedean derivations on $\mathrm{GL}_2(\mathbb{A}_K)$: one-parameter subgroups supported at different infinite places commute in the adelic group, so the associated derivations commute on functions satisfying the stated continuity and smoothness conditions for words of length at most two. It is used to move Casimir operators at one place past derivations at other places, in [`AutomorphicForm.archCasimirAt_foldr_archDeriv_eq_foldr_archDeriv_archCasimirAt`](thm.html#AutomorphicForm.archCasimirAt_foldr_archDeriv_eq_foldr_archDeriv_archCasimirAt) and [`AutomorphicForm.archCasimirAtComplex_and_archCasimirBarAtComplex_foldr_archDeriv_eq_foldr_archDeriv`](thm.html#AutomorphicForm.archCasimirAtComplex_and_archCasimirBarAtComplex_foldr_archDeriv_eq_foldr_archDeriv); at a single place the corresponding commutators are instead the $\mathfrak{sl}_2$ relations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_foldr_archDeriv_comm_of_ne_place.lean

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

theorem AutomorphicForm.foldr_archDeriv_comm_of_ne_place
    (K : Type) [Field K] [NumberField K]
    (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    (∀ l, l.length ≤ 2 →
      Continuous (W l φ) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l φ)) ∧
      (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l φ))) →
    ∀ d d' : (Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕ (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex),
      Sum.elim (fun e => e.1) (fun e => e.1) d ≠ Sum.elim (fun e => e.1) (fun e => e.1) d' →
      W [d, d'] φ = W [d', d] φ := by sorry
