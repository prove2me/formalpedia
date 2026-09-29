-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map
-- name    : AlgebraicGeometry.RiemannForm.isConstScalar_pullback_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/200d0c1b-f4d6-50ab-9e1d-d6e7f779beb8
-- title:
--   Constant scalar multiplications are preserved by pullback over the base
-- statement:
--   Let $k$ be a field, $A$ a scheme, and $f : A \to \operatorname{Spec} k$ a morphism. For a sheaf of modules $M$ on $A$ and an endomorphism $\sigma : M \to M$, the predicate `IsConstScalar f \sigma c`, for $c \in k$, asserts that for every open $U \subseteq A$ and every section $s \in \Gamma(M, U)$ one has $\sigma_U(s) = r|_U \cdot s$, where $r \in \Gamma(A, \mathcal{O}_A)$ is the image of $c$ under $f^\sharp$ on global sections (i.e. $c$ transported to $\Gamma(\operatorname{Spec} k, \mathcal{O})$ by the inverse of `Scheme.ΓSpecIso` and then pushed through `f.appTop`), and $r|_U$ is its restriction along $U \le \top$. The theorem states: given in addition an endomorphism $g : A \to A$ of the scheme $A$ with $g$ followed by $f$ equal to $f$, and given $\sigma : M \to M$ and $c \in k$ with `IsConstScalar f \sigma c`, the image of $\sigma$ under the pullback functor `Scheme.Modules.pullback g` on module sheaves, an endomorphism of $g^{*}M$, again satisfies `IsConstScalar f` with the same constant $c$.
--
--   This is the statement that multiplication by a constant from the base is stable under inverse image along a morphism commuting with the structure morphism to $\operatorname{Spec} k$. It is used repeatedly in the construction of the Riemann form / level pairing, where $g$ is a translation or a multiplication-by-$m$ map over the base, for instance by [`AlgebraicGeometry.RiemannForm.existsUnique_isLevelPairingValue`](thm.html#AlgebraicGeometry.RiemannForm.existsUnique_isLevelPairingValue) and [`AlgebraicGeometry.RiemannForm.forall_isLevelPairingValue_one_iff_nonempty_pullback_translation_iso`](thm.html#AlgebraicGeometry.RiemannForm.forall_isLevelPairingValue_one_iff_nonempty_pullback_translation_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_isConstScalar_pullback_map.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.isConstScalar_pullback_map
    (k : Type) [Field k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (g : A ⟶ A) (hg : g ≫ f = f) {M : A.Modules} {σ : M ⟶ M} {c : k} (hσ : IsConstScalar f σ c) :
    IsConstScalar f ((Scheme.Modules.pullback g).map σ) c := by sorry
