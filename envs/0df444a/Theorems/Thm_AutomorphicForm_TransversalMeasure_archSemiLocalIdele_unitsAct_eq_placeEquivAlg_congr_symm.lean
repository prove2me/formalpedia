-- Prove2me | Theorems.Thm_AutomorphicForm_TransversalMeasure_archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm
-- name    : AutomorphicForm.TransversalMeasure.archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/1790ce08-f7aa-55ee-aba7-aacb0f6990e3
-- title:
--   Galois action on archimedean semi-local idele components
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$ that is Galois over $K$, and let $D$ be an idele Galois descent datum for $L/K$, i.e. a monoid homomorphism $\mathrm{act}$ from $L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, compatible with the diagonal map of $L$ (each $\mathrm{act}\,g$ sends the image of $x \in L$ to the image of $g x$) and with each $\mathrm{act}\,g$ continuous. Fix $\sigma : L \simeq_{\mathrm{alg}[K]} L$, an infinite place $v$ of $K$, and a unit $t$ of $\mathbb{A}_L$. Write $\mathrm{arch}_v$ for the homomorphism `archSemiLocalIdele` that takes a unit of $\mathbb{A}_L$, projects to its infinite-adelic component, and evaluates at the infinite places $w$ of $L$ with $w \circ (\text{algebraMap } K\,L) = v$, giving a unit of $\prod_{w \mid v} L_w$; and write $\Psi_v =$ `placeEquivAlg` for the $K_v$-algebra isomorphism $K_v \otimes_K L \cong \prod_{w \mid v} L_w$. Then, as functions on $\{w : w|v\}$, the underlying element of $\mathrm{arch}_v(\mathrm{unitsAct}\,D\,\sigma\,t)$ — that is, of $\mathrm{arch}_v$ applied to $(\mathrm{act}\,\sigma)(t)$ — equals $\Psi_v\bigl((\mathrm{id}_{K_v} \otimes \sigma)\,\Psi_v^{-1}(\mathrm{arch}_v(t))\bigr)$.
--
--   This is the archimedean half of the statement that, under the base-change identification $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$, the Galois action on ideles is $\mathrm{id} \otimes \sigma$; in semi-local coordinates at an infinite place $v$ it says that $\sigma$ acts on $\prod_{w \mid v} L_w$ through the transport of $\mathrm{id}_{K_v} \otimes \sigma$ along $\Psi_v$, hence permutes the factors isometrically. It is used in the analysis of twisted Bruhat transversals, where archimedean component moduli must be controlled under the Galois twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TransversalMeasure_archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm.lean

import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_ArchSemilocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped NumberField.LiesOver in
attribute [local instance] M4aHerbrand.ArchSemilocal.extLiesOver in

theorem AutomorphicForm.TransversalMeasure.archSemiLocalIdele_unitsAct_eq_placeEquivAlg_congr_symm
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (v : InfinitePlace K)
    (t : (AdeleRing (𝓞 L) L)ˣ) :
    ((AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t) :
        ((w : v.Extension L) → w.1.Completion)ˣ) : (w : v.Extension L) → w.1.Completion) =
      M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v
        ((Algebra.TensorProduct.congr (AlgEquiv.refl : v.Completion ≃ₐ[v.Completion] v.Completion) σ)
          ((M4aHerbrand.ArchSemilocal.placeEquivAlg (K := K) (L := L) v).symm
            ((AutomorphicForm.TransversalMeasure.archSemiLocalIdele K L v t : ((w : v.Extension L) → w.1.Completion)ˣ) :
              (w : v.Extension L) → w.1.Completion))) := by sorry
