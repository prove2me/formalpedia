-- Prove2me | Theorems.Thm_Algebra_IsUnramifiedAt_isRegularLocalRing_localization_of_ne_maximalIdeal
-- name    : Algebra.IsUnramifiedAt.isRegularLocalRing_localization_of_ne_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/7f01548f-a725-5c62-a842-4c6eed41db2f
-- title:
--   Regularity at non-maximal primes of a finite unramified algebra
-- statement:
--   Let $R_0$ be a Noetherian local domain such that for every prime ideal $\mathfrak r$ of $R_0$ with $\mathfrak r \neq \mathfrak m_{R_0}$ the localization $(R_0)_{\mathfrak r}$ is a regular local ring, and such that $\operatorname{ringKrullDim} R_0 \le 2$; let $K_0$ be a fraction field of $R_0$. Let $B$ be a Noetherian commutative ring which is an $R_0$-algebra and finite as an $R_0$-module, and let $F$ be a commutative ring carrying compatible $B$-, $R_0$- and $K_0$-algebra structures (the towers $R_0 \to B \to F$ and $R_0 \to K_0 \to F$ being scalar towers) which is a localization of $B$ at the image in $B$ of the non-zerodivisors of $R_0$, so that $F$ plays the role of $B \otimes_{R_0} K_0$; assume the structure map $B \to F$ is injective and $F$ is reduced. Assume finally that $B$ is unramified over $R_0$ at every non-maximal prime of $B$, in the sense of `Algebra.IsUnramifiedAt`. Then for every prime ideal $\mathfrak p$ of $B$ that is not maximal, the localization $B_{\mathfrak p}$ is a regular local ring.
--
--   This is the statement that a module-finite, generically reduced algebra over a base which is regular away from its closed point and of dimension at most $2$ is itself regular away from its closed points, provided it is unramified there. It is used in the analysis of the local structure of a stable model at a supersingular point: it feeds [`IsLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_moduleFinite_of_isUnramifiedAt`](thm.html#IsLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_moduleFinite_of_isUnramifiedAt) and the identification of the completed local ring with a crossing model, [`ModularCurve.UVCrossingModel.exists_ringEquiv_adicCompletion_uvCrossingModel_of_moduleFinite_of_isUnramifiedAt_of_isGalois`](thm.html#ModularCurve.UVCrossingModel.exists_ringEquiv_adicCompletion_uvCrossingModel_of_moduleFinite_of_isUnramifiedAt_of_isGalois).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_IsUnramifiedAt_isRegularLocalRing_localization_of_ne_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct

theorem Algebra.IsUnramifiedAt.isRegularLocalRing_localization_of_ne_maximalIdeal
    {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
    (hR : ∀ (𝔯 : Ideal R₀) [𝔯.IsPrime], 𝔯 ≠ IsLocalRing.maximalIdeal R₀ →
      IsRegularLocalRing (Localization.AtPrime 𝔯))
    (hdim : ringKrullDim R₀ ≤ (2 : WithBot ℕ∞))
    (K₀ : Type*) [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    {B : Type*} [CommRing B] [IsNoetherianRing B] [Algebra R₀ B] [Module.Finite R₀ B]
    (F : Type*) [CommRing F] [Algebra B F] [Algebra R₀ F] [Algebra K₀ F]
    [IsScalarTower R₀ B F] [IsScalarTower R₀ K₀ F]
    [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) F]
    (hinj : Function.Injective (algebraMap B F)) [IsReduced F]
    (hB : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ¬ 𝔭.IsMaximal → Algebra.IsUnramifiedAt R₀ 𝔭) :
    ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ¬ 𝔭.IsMaximal → IsRegularLocalRing (Localization.AtPrime 𝔭) := by sorry
