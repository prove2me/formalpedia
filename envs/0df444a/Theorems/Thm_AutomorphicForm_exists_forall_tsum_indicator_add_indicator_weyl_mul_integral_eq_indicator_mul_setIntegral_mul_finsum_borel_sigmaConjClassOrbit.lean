-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_tsum_indicator_add_indicator_weyl_mul_integral_eq_indicator_mul_setIntegral_mul_finsum_borel_sigmaConjClassOrbit
-- name    : AutomorphicForm.exists_forall_tsum_indicator_add_indicator_weyl_mul_integral_eq_indicator_mul_setIntegral_mul_finsum_borel_sigmaConjClassOrbit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/ffb8d34a-c767-5b62-bd0d-434324ac5c65
-- title:
--   Twisted-class truncation weights collapse onto the Borel part
-- statement:
--   Let $L/K$ be an extension of number fields that is Galois, let $\nu$ be a Haar measure on the idele units $(\mathbb A_L)^\times$ for its Borel $\sigma$-algebra, and let $\Omega$ be a fundamental domain for the action of the image of $L^\times$ in $(\mathbb A_L)^\times$ on $(\mathbb A_L)^\times$ with respect to $\nu$. Let $D$ be an idele Galois descent datum, i.e. a homomorphism $\mathrm{Gal}(L/K)\to\mathrm{Aut}_{\mathrm{ring}}(\mathbb A_L)$ which is continuous in each argument and compatible with $L\to\mathbb A_L$, and let $\sigma\in\mathrm{Gal}(L/K)$ be such that every element of the group lies in the subgroup of integer powers of $\sigma$. Let $\xi$ be a homomorphism from the full subgroup of $(\mathbb A_L)^\times$ to $\mathbb C^\times$, continuous as a $\mathbb C$-valued function and trivial on the principal ideles. Fix reals $c>0$, $u$, $d_1$, $d_2$, a compact set $T_c\subseteq\mathrm{GL}_2(\mathbb A_L)$, and $\delta_0\in\mathrm{GL}_2(L)$ with vanishing off-diagonal entries and $N_{L/K}(\delta_{0,00}/\delta_{0,11})\neq 1$. Let $I\subseteq\mathrm{GL}_2(L)$ be the set of $\delta$ for which some $g$ satisfies $\delta_0^{-1}(g^{-1}\delta\,\sigma(g))\in Z(\mathrm{GL}_2(L))$, where $\sigma$ acts entrywise, let $\Lambda$ be a subgroup consisting exactly of those $\gamma$ with $\delta_0^{-1}(\gamma\delta_0\sigma(\gamma)^{-1})\in Z(\mathrm{GL}_2(L))$, and let $r:\iota\to\mathrm{GL}_2(L)$ be such that each $\gamma$ satisfies $r_i^{-1}\gamma\in\Lambda$ for exactly one $i$. Let $\varphi:\mathrm{GL}_2(\mathbb A_L)\to\mathbb C$ be continuous with compact support. Write $\iota$ for the entrywise map $\mathrm{GL}_2(L)\to\mathrm{GL}_2(\mathbb A_L)$, $c(z)=\mathrm{diag}(z,z)$, $\sigma_{\mathbb A}$ for the entrywise action of $D(\sigma)$, $w$ for the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and $H$ for the adelic height, the product over the infinite places of the local heights of the archimedean components raised to the place multiplicities, times the finite product over the finite places of the local finite heights. Then there is $R_0\in\mathbb R$ such that for every $R\ge R_0$ and every $x$ of the form $g\,y$ with $y\in T_c$ and $g$ in the centre-cut Siegel set for $(c,u,d_1,d_2)$ — its finite part integral, all archimedean local heights at least $c$, all window quantities at most $u^2$, and all archimedean determinant norms in $[d_1,d_2]$ — the function $z\mapsto\xi(z)\sum^{\mathrm f}_{\delta}\varphi\bigl(x^{-1}\iota(\delta)\,\sigma_{\mathbb A}(c(z)x)\bigr)$, the finite sum being over those $\delta\in I$ with vanishing lower-left entry, is integrable on $\Omega$ for $\nu$, and, setting $y_i=\iota(r_i)^{-1}x$, $$\sum_{i}\Bigl(\mathbf 1[H(y_i)>e^R]+\mathbf 1[H(w\,y_i)>e^R]\Bigr)\int \xi(z)\,\varphi\bigl(y_i^{-1}\iota(\delta_0)\,\sigma_{\mathbb A}(c(z)y_i)\bigr)\,\mathrm d\nu(z)=\mathbf 1[H(x)>e^R]\int_{\Omega}\xi(z)\sum^{\mathrm f}_{\delta}\varphi\bigl(x^{-1}\iota(\delta)\,\sigma_{\mathbb A}(c(z)x)\bigr)\,\mathrm d\nu(z),$$ the inner integrals on the left being over all of $(\mathbb A_L)^\times$.
--
--   This is the regrouping step on the geometric side of a twisted trace formula for $\mathrm{GL}(2)$: for points high in a centre-cut Siegel set translated by a compact set, the two cuspidal truncation indicators attached to the cosets of the stabiliser $\Lambda$ of a hyperbolic twisted class add up to the single truncated central unfolding of the upper-triangular part of that class. It is used in the construction of the truncated twisted orbital contribution, where the difference between the truncated kernel and its unipotent correction terms is shown to vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_tsum_indicator_add_indicator_weyl_mul_integral_eq_indicator_mul_setIntegral_mul_finsum_borel_sigmaConjClassOrbit.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem AutomorphicForm.exists_forall_tsum_indicator_add_indicator_weyl_mul_integral_eq_indicator_mul_setIntegral_mul_finsum_borel_sigmaConjClassOrbit
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ x ∈ ⋃ y ∈ Tc, (· * y) '' AutomorphicForm.WindowedSiegel.centreCutSiegelSet L c u d₁ d₂,
        IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL ∧
        (∑' i : ι,
          (Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x) +
            Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
          ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
              AutomorphicForm.sigmaAdelicAct K L D σ
                (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)))
            ∂νZL) =
        Set.indicator {y : AutomorphicForm.AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
            (fun _ => (1 : ℂ)) x *
          ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I},
              φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL := by sorry
