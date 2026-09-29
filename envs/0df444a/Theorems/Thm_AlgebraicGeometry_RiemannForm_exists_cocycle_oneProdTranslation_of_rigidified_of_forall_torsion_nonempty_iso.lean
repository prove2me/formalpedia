-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso
-- name    : AlgebraicGeometry.RiemannForm.exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/2c96e52b-8f38-5c48-aab1-3f6613dfd15f
-- title:
--   Cocycle of translation isomorphisms for a rigidified bundle
-- statement:
--   Let $k$ be an algebraically closed field, $f : A \to \operatorname{Spec} k$ a morphism of schemes, $L$ a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ t = f\}$ of sections over $k$-schemes, compatible with base change), $hc$ a witness that $L$ is commutative, and $hA$ a witness that $f$ is smooth and proper with connected fibres and admits a relative group law. Let $g$ be a natural number such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and let $n$ be a natural number. Let $\mathcal{Q}$ be a module on $A \times_k A$ that is invertible, in the sense that each point has an open neighbourhood $U$ with $\mathcal{Q}|_U$ isomorphic to the unit sheaf of modules. Write $\sigma_Q := \mathrm{pullback.lift}$ of the first projection and of the second projection followed by translation by $Q$, that is $1 \times T_Q : A \times_k A \to A \times_k A$, for a $k$-point $Q$ of $L$ (the group $L.\mathrm{AlgPoints}\ hc\ k$ of sections over $\operatorname{Spec} k$, written additively), and similarly write $\iota_0$ for the graph map $A \times_k \operatorname{Spec} k \to A \times_k A$ attached to the zero section. Assume that the pullback of $\mathcal{Q}$ along the symmetry of $A\times_k A$, restricted along $\iota_0$, is isomorphic to the monoidal unit, and that for every $Q$ with $nQ = 0$ there exists at least one isomorphism $\sigma_Q^{*}\mathcal{Q} \cong \mathcal{Q}$. The conclusion is that these unrelated isomorphisms can be chosen coherently: there is a family $\psi_Q : \mathcal{Q} \cong \sigma_Q^{*}\mathcal{Q}$, indexed by the pairs consisting of $Q$ and a proof that $nQ = 0$, such that (i) for any equality $e_0 : \sigma_0 = \mathrm{id}$, $\psi_0$ is the canonical isomorphism obtained from the identity-pullback isomorphism and from $e_0$, and (ii) for all $P, Q$ with $nP = nQ = n(P+Q) = 0$ and any equality $e_{P,Q} : \sigma_{P+Q} = \sigma_P$ followed by $\sigma_Q$, one has $\psi_{P+Q}$ equal to $\psi_P$ followed by $\sigma_P^{*}\psi_Q$, followed by the comparison isomorphism $\sigma_P^{*}\sigma_Q^{*}\mathcal{Q} \cong (\sigma_P \text{ then } \sigma_Q)^{*}\mathcal{Q}$ and by the isomorphism induced by $e_{P,Q}$. The equalities $e_0$ and $e_{P,Q}$ are quantified over rather than produced, so that the statement contains no inline proofs.
--
--   This is the step that upgrades mere existence of isomorphisms $\sigma_Q^{*}\mathcal{Q}\cong\mathcal{Q}$, for $Q$ in the $n$-torsion of $A(k)$, to a genuine cocycle for the action $Q \mapsto 1\times T_Q$ of $A[n](k)$ on $A\times_k A$, rigidity along $\{0\}\times A$ removing the $k^{\times}$-ambiguity in each isomorphism. It is used to produce the descent datum for a rigidified line bundle on $A\times_k A$ along $1\times[n]$, in the construction of the pairing attached to a polarisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.RiemannForm.exists_cocycle_oneProdTranslation_of_rigidified_of_forall_torsion_nonempty_iso
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ)
    (𝓠 : (pullback f f).Modules) (h𝓠 : Scheme.Modules.IsInvertible 𝓠)
    (hrig : Nonempty ((Scheme.Modules.pullback (sliceAt f (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))).obj
        ((Scheme.Modules.pullback (pullbackSymmetry f f).hom).obj 𝓠) ≅ 𝟙_ _))
    (hinv : ∀ Q : L.AlgPoints hc k, n • Q = 0 →
      Nonempty ((Scheme.Modules.pullback
        (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).obj 𝓠 ≅ 𝓠)) :
    ∃ ψ : ∀ Q : L.AlgPoints hc k, n • Q = 0 →
        (𝓠 ≅ (Scheme.Modules.pullback
          (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).obj 𝓠),
      (∀ (h0 : n • (0 : L.AlgPoints hc k) = 0)
          (e0 : (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (0 : L.AlgPoints hc k)))
          (by rw [Category.assoc, translation_over]; exact pullback.condition)) = 𝟙 (pullback f f)),
        ψ 0 h0 = ((Scheme.Modules.pullbackId (pullback f f)).app 𝓠).symm ≪≫ ((Scheme.Modules.pullbackCongr e0).app 𝓠).symm) ∧
      (∀ (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (hPQ : n • (P + Q) = 0)
          (ePQ : (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint (P + Q)))
          (by rw [Category.assoc, translation_over]; exact pullback.condition)) =
            (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
          (by rw [Category.assoc, translation_over]; exact pullback.condition)) ≫
            (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))),
        ψ (P + Q) hPQ =
          ψ P hP ≪≫
            (Scheme.Modules.pullback (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).mapIso (ψ Q hQ) ≪≫
            (Scheme.Modules.pullbackComp (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))
              (pullback.lift (pullback.fst f f) (pullback.snd f f ≫ translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))
          (by rw [Category.assoc, translation_over]; exact pullback.condition))).app 𝓠 ≪≫
            ((Scheme.Modules.pullbackCongr ePQ).app 𝓠).symm) := by sorry
