-- Prove2me | Theorems.Thm_AutomorphicForm_semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
-- name    : AutomorphicForm.semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/ccb829b4-5f82-5a93-bb63-6c068e1a6207
-- title:
--   Semi-local evaluation intertwines the idèlic Galois action with σ⊗ 1
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$ such that $L/K$ is Galois, let $D$ be an idèlic Galois descent datum for $\mathcal{O}_L$, $K$, $L$ — that is, a monoid homomorphism $D.\mathrm{act}$ from $\mathrm{Gal}(L/K) = L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of the adèle ring $\mathbb{A}_L$, compatible with the structure map $L \to \mathbb{A}_L$ in the sense that $D.\mathrm{act}(g)$ carries $\mathrm{algebraMap}(x)$ to $\mathrm{algebraMap}(g x)$, and continuous for each $g$ — let $\sigma \in \mathrm{Gal}(L/K)$, and let $v$ be a height-one prime of $\mathcal{O}_K$. Write $\mathrm{ev}_v \colon \mathbb{A}_{L,\mathrm{f}} \to L \otimes_K K_v$ for the semi-local evaluation, namely the tuple of the evaluations at the primes $w$ of $\mathcal{O}_L$ lying under $v$ followed by the inverse of the base-change isomorphism $L \otimes_K K_v \cong \prod_{w \mid v} L_w$, and $\sigma \otimes 1$ for `Algebra.TensorProduct.congr` applied to $\sigma$ and the identity of $K_v$. The conclusion is a conjunction of three assertions. First, for every adèle $x$ of $L$, $\mathrm{ev}_v$ of the finite part of $D.\mathrm{act}(\sigma)(x)$ equals $(\sigma \otimes 1)$ applied to $\mathrm{ev}_v$ of the finite part of $x$. Second, for every idèle $t \in \mathbb{A}_L^\times$, the image in $L \otimes_K K_v$ of the semi-local idèle of $D.\mathrm{unitsAct}(\sigma)(t)$ (the unit-group automorphism induced by $D.\mathrm{act}(\sigma)$), obtained by taking the finite part of the idèle and applying $\mathrm{ev}_v$ on units, equals $(\sigma \otimes 1)$ of the image of the semi-local idèle of $t$. Third, for every $g \in \mathrm{GL}_2(\mathbb{A}_L)$ and all $i, j \in \{0,1\}$, the $(i,j)$ entry of the semi-local component at $v$ of the finite part of $\mathrm{sigmaAdelicAct}$ of $g$ (the entrywise action of $D.\mathrm{act}(\sigma)$ on $\mathrm{GL}_2$) equals $(\sigma \otimes 1)$ applied to the $(i,j)$ entry of the semi-local component at $v$ of the finite part of $g$.
--
--   This is the compatibility, at a finite place $v$ of $K$, between the Galois action on the adèles of $L$ and the identification $L \otimes_K K_v \cong \prod_{w \mid v} L_w$, under which the action becomes $\sigma \otimes 1$; the proof uses the uniqueness of the descent datum, [`M4aHerbrand.subsingleton_ideleGaloisDescent`](thm.html#M4aHerbrand.subsingleton_ideleGaloisDescent). The three forms — for adèles, for idèles, and entrywise for $\mathrm{GL}_2$ — are what allows support and invariance statements for $\sigma$-twisted adèlic integrals to be reduced to the semi-local algebra place by place, and they are cited in the analysis of the unipotent terms of the twisted trace formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.semiLocalEval_act_eq_congr_and_semiLocalIdele_unitsAct_and_semiLocalComponent_sigmaAdelicAct
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) :
    (∀ x : AdeleRing (𝓞 L) L,
      AutomorphicForm.semiLocalEval K L v ((D.act σ : RingAut (AdeleRing (𝓞 L) L)) x).2 =
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
          (AutomorphicForm.semiLocalEval K L v x.2)) ∧
    (∀ t : (AdeleRing (𝓞 L) L)ˣ,
      ((AutomorphicForm.TransversalMeasure.semiLocalIdele K L v (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t) :
          (L ⊗[K] v.adicCompletion K)ˣ) : L ⊗[K] v.adicCompletion K) =
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
          ((AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t : (L ⊗[K] v.adicCompletion K)ˣ) :
            L ⊗[K] v.adicCompletion K)) ∧
    (∀ (g : AutomorphicForm.AdelicGL2 (𝓞 L) L) (i j : Fin 2),
      ((AutomorphicForm.semiLocalComponent K L v
          (NumberField.AdelicLevel.glFin (𝓞 L) L (AutomorphicForm.sigmaAdelicAct K L D σ g)) :
          GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j =
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K))
          (((AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L g) :
            GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) i j)) := by sorry
