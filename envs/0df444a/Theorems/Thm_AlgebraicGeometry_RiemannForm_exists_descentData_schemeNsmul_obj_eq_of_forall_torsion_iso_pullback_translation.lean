-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_descentData_schemeNsmul_obj_eq_of_forall_torsion_iso_pullback_translation
-- name    : AlgebraicGeometry.RiemannForm.exists_descentData_schemeNsmul_obj_eq_of_forall_torsion_iso_pullback_translation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/5950d79e-0efa-5a83-9ed6-4421269ef2bc
-- title:
--   Translation cocycle over A[n] yields descent datum along [n]
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a scheme over $k$, and let $L$ be a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over arbitrary $t : T \to \operatorname{Spec} k$, compatible with base change, with $L$ commutative (`hc`). Assume the bundle `AbelianSchemePropertyBundle` for $f$: $f$ is smooth and proper, every fibre $f^{-1}(s)$ is connected, and $f$ admits a relative group law; assume further that all fibres have topological Krull dimension equal to a fixed $g \in \mathbb{N}$. Let $n \in \mathbb{N}$ with $n \neq 0$ in $k$, and let $M$ be an $\mathcal{O}_A$-module. Write $T_P : A \to A$ for the translation $\mathrm{id} \cdot \mathrm{const}_P$ attached to a point $P$ of the additive group $L.\mathrm{AlgPoints}$ of $k$-sections of $f$. Suppose given, for every $P$ with $nP = 0$, an isomorphism $\psi_P : M \cong T_P^{*}M$ such that $\psi_0$ is the canonical isomorphism $M \cong \mathrm{id}^{*}M \cong T_0^{*}M$, and such that for all $n$-torsion $P, Q$ the cocycle relation $\psi_{P+Q} = \psi_P$ followed by $T_P^{*}\psi_Q$, the comparison $T_P^{*}T_Q^{*}M \cong (T_P \text{ followed by } T_Q)^{*}M$ and the identification $T_PT_Q = T_{P+Q}$ holds. Then there exists a descent datum $D$ for the pseudofunctor of $\mathcal{O}$-module categories (composed with `Bicategory.Adj.forget₁`) relative to the one-element family consisting of the multiplication-by-$n$ map $L.\mathrm{schemeNsmul}\, n : A \to A$, whose object at the unique index is $M$.
--
--   This is the descent step in the construction of a line bundle (or module) on $A$ from a level structure: a cocycle of translation isomorphisms indexed by the $n$-torsion points of an abelian variety over an algebraically closed field constitutes a descent datum for $\mathcal{O}$-modules along the isogeny $[n] : A \to A$. It is used in the construction of pullbacks along $[2]$ attached to a level subgroup in the polarisation material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_exists_descentData_schemeNsmul_obj_eq_of_forall_torsion_iso_pullback_translation.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ThetaGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.exists_descentData_schemeNsmul_obj_eq_of_forall_torsion_iso_pullback_translation
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (M : A.Modules)
    (ψ : ∀ P : L.AlgPoints hc k, n • P = 0 →
        (M ≅ (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).obj M))
    (hψ0 : ∀ h0 : n • (0 : L.AlgPoints hc k) = 0,
        ψ 0 h0 = ((Scheme.Modules.pullbackId A).app M).symm ≪≫
          ((Scheme.Modules.pullbackCongr (translation_toPoint_zero f L hc)).app M).symm)
    (hψadd : ∀ (P Q : L.AlgPoints hc k) (hP : n • P = 0) (hQ : n • Q = 0) (hPQ : n • (P + Q) = 0),
        ψ (P + Q) hPQ =
          ψ P hP ≪≫
            (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).mapIso (ψ Q hQ) ≪≫
            (Scheme.Modules.pullbackComp (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))
              (translation f L (RelativeGroupLaw.AlgPoints.toPoint Q))).app M ≪≫
            ((Scheme.Modules.pullbackCongr (translation_toPoint_add f L hc P Q)).app M).symm) :
    ∃ D : ((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).DescentData (fun _ : Unit => L.schemeNsmul n),
      ∀ i, D.obj i = M := by sorry
