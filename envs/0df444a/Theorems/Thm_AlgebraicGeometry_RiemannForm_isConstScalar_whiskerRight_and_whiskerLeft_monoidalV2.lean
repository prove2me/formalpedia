-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2
-- name    : AlgebraicGeometry.RiemannForm.isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/f4615707-afe8-5760-959b-86060379db2f
-- title:
--   Constant scalars are preserved by whiskering
-- statement:
--   Let $k$ be a field, let $A$ be a scheme (in the bottom universe) and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes. For a sheaf of $\mathcal{O}_A$-modules $M$, say that an endomorphism $\sigma$ of $M$ is a constant scalar with value $c \in k$, written `IsConstScalar f σ c`, if for every open $U \subseteq A$ and every section $s \in \Gamma(M, U)$ one has $\sigma_U(s) = a|_U \cdot s$, where $a \in \Gamma(A, A)$ is the global function obtained by pulling back $c$ along $f$ (that is, transporting $c$ through the inverse of the isomorphism $k \cong \Gamma(\operatorname{Spec} k)$ and applying $f$ on global sections), and $a|_U$ is its restriction to $U$ along the inclusion $U \subseteq A$. The theorem asserts: given such an $f$, a sheaf of modules $M$ with an endomorphism $\sigma$, an element $c \in k$ with `IsConstScalar f σ c`, and a further sheaf of $\mathcal{O}_A$-modules $K$, both whiskerings are again constant scalars with the same value $c$, namely $\sigma \rhd K$ on $M \otimes K$ and $K \lhd \sigma$ on $K \otimes M$, for the monoidal structure on $A.\mathrm{Modules}$.
--
--   This is the statement that multiplication by a constant from the base field passes through the tensor product of sheaves of modules, in the form needed for the monoidal structure used in the treatment of Riemann forms and level pairings; it is cited in the verification that a level pairing value is preserved under pushforward of a point and an isomorphism of the pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_SheafOfModules_MonoidalV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.isConstScalar_whiskerRight_and_whiskerLeft_monoidalV2
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    {M : A.Modules} (σ : M ⟶ M) (c : k) (h : IsConstScalar f σ c) (K : A.Modules) :
    IsConstScalar f (σ ▷ K) c ∧ IsConstScalar f (K ◁ σ) c := by sorry
