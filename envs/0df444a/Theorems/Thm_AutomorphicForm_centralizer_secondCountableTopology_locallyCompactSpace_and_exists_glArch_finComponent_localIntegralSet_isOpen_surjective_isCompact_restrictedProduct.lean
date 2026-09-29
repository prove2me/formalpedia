-- Prove2me | Theorems.Thm_AutomorphicForm_centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct
-- name    : AutomorphicForm.centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/e328a41c-0419-58da-becc-82dbec083aa4
-- title:
--   Centralisers in adelic GL₂ as a restricted product
-- statement:
--   Let $K$ be a number field and let $\gamma \in GL_2(\mathbb{A}_K)$ be arbitrary. Write $T = Z(\{\gamma\})$ inside $GL_2(\mathbb{A}_K)$, $T_\infty = Z(\{\gamma_\infty\})$ inside $GL_2(K_\infty)$ for the image $\gamma_\infty$ of $\gamma$ under `AdelicLevel.glArch`, and, for each finite place $v$, $T_v = Z(\{\gamma_v\})$ inside $GL_2(K_v)$ for the $v$-component $\gamma_v$ of the finite part of $\gamma$ (`AdelicLevel.finComponent` of `AdelicLevel.glFin`); all carry the subspace topology. The assertion is: $T$, $T_\infty$ and every $T_v$ are second countable and locally compact; and there exist group homomorphisms $q : T \to T_\infty$ and $p_v : T \to T_v$ and subgroups $U_v \le T_v$ such that $q$ and each $p_v$ are induced by `glArch` and by `finComponent` of `glFin` on underlying matrices, each $U_v$ has underlying set the intersection of $T_v$ with [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100), i.e. with the set of $g \in GL_2(K_v)$ such that both $g$ and $g^{-1}$ lie in the integral matrix set of `v.adicCompletionIntegers K`; $q$ and all $p_v$ are continuous; each $U_v$ is compact and open; for every finite set $S$ of finite places $\{b \in T : p_v(b) \in U_v \text{ for all } v \notin S\}$ is open; for every such $S$, every $y \in T_\infty$ and every family $(x_v) \in \prod_v T_v$ with $x_v \in U_v$ for $v \notin S$ there is $b \in T$ with $q(b) = y$ and $p_v(b) = x_v$ for all $v$; and for every compact $D \subseteq T_\infty$ and compact sets $C_v \subseteq T_v$ with $C_v = U_v$ outside a finite set of places, the box $\{b \in T : q(b) \in D,\ p_v(b) \in C_v \text{ for all } v\}$ is compact.
--
--   This packages the centraliser of an arbitrary element of $GL_2(\mathbb{A}_K)$ as a restricted product of its archimedean centraliser and its local centralisers with respect to the compact open subgroups $T_v \cap GL_2(\mathcal{O}_v)$, in exactly the form required by the abstract factorisation of Haar measure on a restricted product. It is invoked by the results on orbital and weighted orbital integrals over centralisers of diagonal elements `diagUnits2` times a central scalar.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.centralizer_secondCountableTopology_locallyCompactSpace_and_exists_glArch_finComponent_localIntegralSet_isOpen_surjective_isCompact_restrictedProduct
    (K : Type) [Field K] [NumberField K] (γ : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    SecondCountableTopology (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) ∧ LocallyCompactSpace (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) ∧
    SecondCountableTopology (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) ∧ LocallyCompactSpace (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) ∧
    (∀ v : HeightOneSpectrum (𝓞 K), SecondCountableTopology (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) ∧ LocallyCompactSpace (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))) ∧
    ∃ (q : (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) →* (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
      (p : ∀ v : HeightOneSpectrum (𝓞 K), (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))) →* (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))
      (U : ∀ v : HeightOneSpectrum (𝓞 K), Subgroup (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))),
      (∀ t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))), ((q t : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) : GL (Fin 2) (InfiniteAdeleRing K)) = AdelicLevel.glArch (𝓞 K) K (t : GL (Fin 2) (AdeleRing (𝓞 K) K))) ∧
      (∀ (v : HeightOneSpectrum (𝓞 K)) (t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))),
        ((p v t : AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))) : GL (Fin 2) (v.adicCompletion K)) =
          AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (t : GL (Fin 2) (AdeleRing (𝓞 K) K)))) ∧
      (∀ v : HeightOneSpectrum (𝓞 K),
        ((U v : Subgroup (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))) : Set (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))) = Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) ∧
      Continuous q ∧ (∀ v, Continuous (p v)) ∧
      (∀ v, IsCompact ((U v : Subgroup (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))) : Set (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))) ∧
      (∀ v, IsOpen ((U v : Subgroup (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))) : Set (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))) ∧
      (∀ Sf : Finset (HeightOneSpectrum (𝓞 K)), IsOpen {b : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) | ∀ v ∉ Sf, p v b ∈ U v}) ∧
      (∀ (Sf : Finset (HeightOneSpectrum (𝓞 K))) (y : Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) (x : ∀ v : HeightOneSpectrum (𝓞 K), AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))),
        (∀ v ∉ Sf, x v ∈ U v) → ∃ b : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))), q b = y ∧ ∀ v, p v b = x v) ∧
      (∀ (D : Set (Subgroup.centralizer ({AdelicLevel.glArch (𝓞 K) K γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))) (C : ∀ v : HeightOneSpectrum (𝓞 K), Set (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))),
        IsCompact D → (∀ v, IsCompact (C v)) →
        {v | C v ≠ ((U v : Subgroup (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ)))) : Set (AutomorphicForm.localCentralizer K v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K γ))))}.Finite →
        IsCompact {b : Subgroup.centralizer ({γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))) | q b ∈ D ∧ ∀ v, p v b ∈ C v}) := by sorry
