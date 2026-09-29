-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi
-- name    : AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/31a97920-434a-5b10-a458-dd862f0399ad
-- title:
--   Positivity of fibrewise h⁰ over a finite product base
-- statement:
--   Fix a natural number $k$ and a family $C : \mathrm{Fin}\,k \to \mathrm{Type}$ of commutative rings, a scheme $A'$ over $\operatorname{Spec}$ of the product ring $\prod_i C_i$ via $f' : A' \to \operatorname{Spec}(\prod_i C_i)$, and an object $\mathcal L$ of $A'.\mathrm{Modules}$. Suppose given schemes $A_i$ with morphisms $f_i : A_i \to \operatorname{Spec} C_i$ and morphisms $v_i : A_i \to A'$ such that for each $i$ the square formed by $v_i$, $f_i$, $f'$ and $\operatorname{Spec}$ of the evaluation homomorphism $\prod_j C_j \to C_i$ is cartesian. Assume further that for every index $i$, every algebraically closed field $K$ and every ring homomorphism $s : C_i \to K$, the quantity $\mathrm{geomFibreH0Finrank}$ of $f_i$ and the pullback of $\mathcal L$ along $v_i$ at $s$ is positive; here $\mathrm{geomFibreH0Finrank}$ denotes the $K$-dimension of the global sections of the pullback of the given module to the fibre product of the structure morphism with $\operatorname{Spec}$ of $s$, the $K$-module structure coming from the induced $K$-algebra structure on the global sections of that fibre. The conclusion is that the same positivity holds for $f'$ and $\mathcal L$: for every algebraically closed field $K$ and every ring homomorphism $\prod_i C_i \to K$, the corresponding geometric-fibre dimension of global sections is positive.
--
--   This is the statement that positivity of $h^0$ on geometric fibres of a polarising module may be checked on the finitely many clopen pieces of a base which is a finite product of rings, the pieces being given as pullbacks along the evaluation homomorphisms. It is used in the construction of canonical polarisation data for fake elliptic curves over a product base, where the polarisation condition is verified factor by factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

theorem AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_pos_of_forall_pullback_of_isPullback_pi
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of (∀ i, C i))) (𝓛 : A'.Modules)
    {Ai : Fin k → Scheme.{0}} (fi : ∀ i, Ai i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Ai i ⟶ A')
    (hv : ∀ i, IsPullback (v i) (fi i) f' (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (hloc : ∀ (i : Fin k) (K : Type) [Field K] [IsAlgClosed K] (sk : C i →+* K),
      0 < Scheme.Modules.geomFibreH0Finrank (fi i) ((Scheme.Modules.pullback (v i)).obj 𝓛) K sk) :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (sk : (∀ i, C i) →+* K), 0 < Scheme.Modules.geomFibreH0Finrank f' 𝓛 K sk := by sorry
