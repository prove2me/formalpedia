-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv
-- name    : AlgebraicGeometry.OModulePresheaf.Leray.nonempty_E2I_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/b0c15a81-df48-5243-a341-5df1d9e5800e
-- title:
--   E₂ page of the Čech–Leray double complex
-- statement:
--   Let $R$ be a commutative ring, let $V'$ and $Z$ be schemes, let $p \colon V' \to Z$ be a morphism, let $\pi_Z \colon Z \to \operatorname{Spec} R$ be a morphism, and let $K$ and $K'$ be ordered affine covers of $Z$ and of $V'$ respectively, each consisting of a finite linearly ordered family of affine opens whose supremum is the whole scheme. Write $C^{\bullet,\bullet} =$ `LerayDblCpx p πZ K K'` for the associated bounded double complex of $R$-modules (terms `biC p πZ K K'`, horizontal and vertical differentials `dH` and `dV`, each squaring to zero and commuting with one another, with all terms subsingleton once either degree reaches the maximum of the cardinalities of the two index types), and write $\mathcal H^b =$ `relHPresheaf p πZ K' b` for the presheaf of $\mathcal O_Z$-modules with $R$-action sending an open $U \subseteq Z$ to the degree-$b$ relative alternating Čech cohomology $\ker(\mathrm{relAltd}\, U\, b)/\mathrm{relAltHB}\, U\, b$ of $K'$ over $U$, with restriction maps induced by those of the relative cochains. Then: for every $b \in \mathbb N$ the $R$-module [`DoubleComplex.E₂I`](def/AlgebraicGeometry_DoubleComplex.html#L163) $C^{\bullet,\bullet}$ in position $(0,b)$, i.e. the second page of the spectral sequence taking vertical cohomology first and then horizontal, admits an $R$-linear isomorphism onto $\check H^0(K,\mathcal H^b) = \ker(\mathcal H^b.d\,K\,0)$ inside the $0$-cochains of $K$; and for all $a, b \in \mathbb N$ the term in position $(a+1,b)$ admits an $R$-linear isomorphism onto $\check H^{a+1}(K,\mathcal H^b) = \ker(\mathcal H^b.d\,K\,(a+1))$ modulo the image of $\mathcal H^b.d\,K\,a$. The two clauses are stated as nonemptiness of the respective types of linear equivalences, so only existence of such isomorphisms is asserted, with no naturality or compatibility; no hypotheses are imposed on $p$ or $\pi_Z$ beyond their being morphisms of schemes, and the splitting into degrees $0$ and $a+1$ reflects that Čech $H^0$ is a submodule of cochains while the higher groups are quotients.
--
--   This is the identification of the second page of the Čech–Leray (Godement) spectral sequence of a morphism with the Čech cohomology of the base cover with coefficients in the relative cohomology presheaves. It is used in the project's finiteness results for Čech cohomology, being cited by [`AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinite_unit_of_isIntegral_of_ih).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv.lean

import Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.LinearAlgebra.Quotient.Pi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.nonempty_E2I_equiv
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) :
    (∀ b : ℕ, Nonempty (DoubleComplex.E₂I (OModulePresheaf.Leray.LerayDblCpx p πZ K K') 0 b
        ≃ₗ[R] (OModulePresheaf.Leray.relHPresheaf p πZ K' b).H0 K)) ∧
      ∀ a b : ℕ, Nonempty (DoubleComplex.E₂I (OModulePresheaf.Leray.LerayDblCpx p πZ K K') (a + 1) b
        ≃ₗ[R] (OModulePresheaf.Leray.relHPresheaf p πZ K' b).HSucc K a) := by sorry
