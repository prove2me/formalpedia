-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
-- name    : AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/8426d521-f47b-5276-9db4-d5057a3dc097
-- title:
--   Čech cohomology of γ^*N agrees with that of γ_*mathcal O_W⊗ N
-- statement:
--   Let $R$ be a commutative ring, let $V$ and $W$ be schemes, let $\pi : V \to \operatorname{Spec} R$ be separated, let $\gamma : W \to V$ be an affine morphism, let $K$ be an ordered affine cover of $V$ (a finite linearly ordered index set $\iota$ together with opens $U_i \subseteq V$ that are affine and cover $V$), and let $N$ be a module over the structure sheaf of $V$. Assume that $N$ is Zariski-locally trivial in the sense that every point $x \in V$ lies in some open $U$ for which the pullback of $N$ along the inclusion $U \hookrightarrow V$ admits an isomorphism to the unit sheaf of modules on $U$. Write $K.\mathrm{comap}\ \gamma$ for the ordered affine cover of $W$ with the same index set and opens $\gamma^{-1}U_i$ (affine since $\gamma$ is affine). Two presheaves of modules over $R$-algebras of sections are compared: on $W$, relative to $\gamma \gg \pi$, the presheaf $U \mapsto \Gamma(\gamma^*N, U)$ of sections of the pullback $(\mathrm{Scheme.Modules.pullback}\ \gamma).\mathrm{obj}\ N$; and on $V$, relative to $\pi$, the presheaf $U \mapsto \Gamma(W, \gamma^{-1}U) \otimes_{\Gamma(V,U)} \Gamma(N,U)$, namely the twist by $N$ of the pushforward along $\gamma$ of the unit presheaf. The conclusion asserts, for the alternating Čech complexes of these presheaves on the respective covers, the existence (as `Nonempty`) of an $R$-linear equivalence between the degree-zero cohomologies $H^0$ (the kernels of the zeroth differentials) and, for every $i \in \mathbb N$, of an $R$-linear equivalence between the degree-$(i+1)$ cohomologies $\ker d^{i+1}/\operatorname{im} d^{i}$. No canonical choice of these equivalences is recorded.
--
--   This is the affine base-change (projection-formula) comparison for Čech complexes: the Čech cohomology of $\gamma^*N$ on the pulled-back cover of $W$ coincides with that of $\gamma_*\mathcal O_W \otimes N$ on the original cover of $V$, for $\gamma$ affine and $N$ locally trivial. It feeds the subsequent statements comparing or computing Čech invariants of pullbacks, including the vanishing statement [`AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_iso_pullback_of_isIso`](thm.html#AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_of_iso_pullback_of_isIso) and the rank comparison [`AlgebraicGeometry.OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso`](thm.html#AlgebraicGeometry.OModulePresheaf.cechFinrank_ofModules_pullback_eq_of_isIso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
    {R : Type u} [CommRing R] {V W : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    (γ : W ⟶ V) [IsAffineHom γ] (K : V.OrderedAffineCover) (N : V.Modules)
    (hN : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    Nonempty ((OModulePresheaf.ofModules (γ ≫ π) ((Scheme.Modules.pullback γ).obj N)).H0 (K.comap γ) ≃ₗ[R]
        ((OModulePresheaf.pushforwardUnit π γ).twist N).H0 K) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules (γ ≫ π) ((Scheme.Modules.pullback γ).obj N)).HSucc
          (K.comap γ) i ≃ₗ[R] ((OModulePresheaf.pushforwardUnit π γ).twist N).HSucc K i) := by sorry
