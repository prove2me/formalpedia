-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_archHaarK_torusFamily_isOrbitalIntegral_centralScalar_mul_diagUnits2_of_isArchTestFactor_of_isLocalTestFn
-- name    : AutomorphicForm.exists_eq_archHaarK_torusFamily_isOrbitalIntegral_centralScalar_mul_diagUnits2_of_isArchTestFactor_of_isLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/c8feb854-4051-5c95-8bd8-ba2e55dce3c0
-- title:
--   Standing data for the split hyperbolic family over K
-- statement:
--   Let $K$ be a number field, let the unit group $\mathbb{A}_K^\times$ of the adele ring carry a measurable structure which is the Borel structure of its topology, let $\nu_{Z_K}$ be a Haar measure on $\mathbb{A}_K^\times$, and let $S_K$ be a finite set of height-one primes of $\mathcal{O}_K$. Let $f_{a,K} : \mathrm{GL}_2(K_\infty) \to \mathbb{C}$ satisfy [`AutomorphicForm.IsArchTestFactor`](def/AutomorphicForm_FactorizableTestFn.html#L27), i.e. there is a map $\Phi$ on $2 \times 2$ matrices over the mixed space of $K$ which is $C^\infty$ over $\mathbb{R}$ and satisfies $f_{a,K}(g) = \Phi(\mathrm{archEntries}(g))$ for all $g$, where $\mathrm{archEntries}(g)$ is the matrix of entries of $g$ transported to the mixed space, and $f_{a,K}$ has compact support. Let $f_{S_K}$ assign to each finite place $v$ a function $\mathrm{GL}_2(K_v) \to \mathbb{C}$, such that for $v \in S_K$ the function $f_{S_K}(v)$ is locally constant with compact support ([`AutomorphicForm.IsLocalTestFn`](def/AutomorphicForm_LocalOrbitalBase.html#L88)). Let $c_{\tau,K}$ be a real number with $c_{\tau,K} > 0$.
--
--   For $u \in K^\times$ and $z \in \mathbb{A}_K^\times$ write $\gamma(u,z) = c(z)\,\mathrm{diag}(u,1) \in \mathrm{GL}_2(\mathbb{A}_K)$, where $c(z)$ is the scalar matrix [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) attached to $z$ and $\mathrm{diag}(u,1) =$ `diagUnits2` applied to the image of $u$ under $K^\times \to \mathbb{A}_K^\times$ and to $1$. Its archimedean component is $\mathrm{glArch}(\gamma(u,z)) \in \mathrm{GL}_2(K_\infty)$ and its component at a finite place $v$ is $\mathrm{finComponent}_v(\mathrm{glFin}(\gamma(u,z))) \in \mathrm{GL}_2(K_v)$, obtained by applying the respective projections of $\mathbb{A}_K$ entrywise.
--
--   The assertion is the existence of the following data: a measure $\nu_A$ on $\mathrm{GL}_2(K_\infty)$ for the Borel structure `glBorelOf`; a real number $c_G$; for each $u \in K^\times$ and $z \in \mathbb{A}_K^\times$ a measure $\tau_G(u,z)$ on the centraliser $Z_{\mathrm{GL}_2(\mathbb{A}_K)}(\gamma(u,z))$ of the singleton $\{\gamma(u,z)\}$, a measure $\tau_A(u,z)$ on the centraliser of $\mathrm{glArch}(\gamma(u,z))$ in $\mathrm{GL}_2(K_\infty)$ for the Borel structure `centralizerBorel`, and for each finite place $v$ a measure $\tau_F(u,z,v)$ on the local centraliser of $\mathrm{finComponent}_v(\mathrm{glFin}(\gamma(u,z)))$ in $\mathrm{GL}_2(K_v)$ for the Borel structure `localCentralizerBorel`; a real number $c_T$; and complex numbers $I_A(u,z)$ and $I_F(u,z,v)$ depending on $u$, $z$ and, in the second case, on $v$. These satisfy the following ten conjuncts.
--
--   First, $\nu_A =$ [`AutomorphicForm.archHaarK K`](def/AutomorphicForm_TwistedOrbital.html#L401), the canonical Haar measure `Measure.haar` on $\mathrm{GL}_2(K_\infty)$ for the Borel structure; thus the archimedean measure is not merely existentially quantified but pinned.
--
--   Second, a restricted-product factorisation of the adelic Haar integral with constant $c_G$: for every finite set $S$ of height-one primes, every $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, every $f_a : \mathrm{GL}_2(K_\infty) \to \mathbb{C}$ and every family $f_S$ of functions on the $\mathrm{GL}_2(K_v)$, if $f_a$ is a.e. strongly measurable for $\nu_A$, if $f_S(v)$ is a.e. strongly measurable for the local Haar measure `localHaar K v` for each $v \in S$, if $f(g) = f_a(\mathrm{glArch}(g)) \cdot \prod_{v \in S} f_S(v)(\mathrm{finComponent}_v(\mathrm{glFin}(g)))$ for every $g$ whose component at each $v \notin S$ lies in the integral set `localIntegralSet K v` (the set of $g_v$ with both $g_v$ and $g_v^{-1}$ having entries in $\mathcal{O}_{K_v}$), and if $f(g) = 0$ for every $g$ failing that integrality at some $v \notin S$, then $\int f \, d(\mathrm{adelicGLHaar})$ equals $c_G \cdot \left(\int f_a \, d\nu_A\right) \cdot \prod_{v \in S} \int f_S(v) \, d(\mathrm{localHaar}\, K\, v)$. No positivity of $c_G$ is asserted.
--
--   Third, for all $u, z$ with $u \neq 1$ in $K$, the measure $\tau_G(u,z)$ is a Haar measure.
--
--   Fourth, for all $u, z$ with $u \neq 1$ and every function $g : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ whatsoever (no measurability or integrability being required), $$\int_{Z(\gamma(u,z))} g(t) \, d\tau_G(u,z) = c_{\tau,K} \int_{\mathbb{A}_K^\times \times \mathbb{A}_K^\times} g(\mathrm{diag}(a,b)) \, d(\nu_{Z_K} \times \nu_{Z_K}),$$ the integrand on the right being evaluated at `diagUnits2 p.1 p.2`.
--
--   Fifth and sixth, for all $u, z$ with $u \neq 1$ the measure $\tau_A(u,z)$ is a Haar measure on the archimedean centraliser, and for all $u, z, v$ with $u \neq 1$ the measure $\tau_F(u,z,v)$ is a Haar measure on the local centraliser at $v$.
--
--   Seventh, for all $u, z, v$ with $u \neq 1$, the measure $\tau_F(u,z,v)$ gives mass $1$ to the preimage of `localIntegralSet K v` under the inclusion of the local centraliser into $\mathrm{GL}_2(K_v)$.
--
--   Eighth, $0 < c_T$.
--
--   Ninth, a restricted-product factorisation of the torus integrals with the single constant $c_T$: for all $u, z$ with $u \neq 1$, for every finite set $S$ of height-one primes, every $W : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, every $W_a : \mathrm{GL}_2(K_\infty) \to \mathbb{C}$ and every family $W_S$ on the $\mathrm{GL}_2(K_v)$, if $t \mapsto W_a(t)$ is a.e. strongly measurable on the archimedean centraliser for $\tau_A(u,z)$, if $t \mapsto W_S(v)(t)$ is a.e. strongly measurable on the local centraliser for $\tau_F(u,z,v)$ for each $v \in S$, if $W(t) = W_a(\mathrm{glArch}(t)) \cdot \prod_{v \in S} W_S(v)(\mathrm{finComponent}_v(\mathrm{glFin}(t)))$ for every $t$ in the adelic centraliser of $\gamma(u,z)$ whose component at each $v \notin S$ lies in `localIntegralSet K v`, and if $W(t) = 0$ for every such $t$ failing that integrality at some $v \notin S$, then $\int W \, d\tau_G(u,z) = c_T \cdot \left(\int W_a \, d\tau_A(u,z)\right) \cdot \prod_{v \in S} \int W_S(v) \, d\tau_F(u,z,v)$.
--
--   Tenth, the orbital integrals. For all $u, z$ with $u \neq 1$, the number $I_A(u,z)$ is an orbital integral of $f_{a,K}$ along $\mathrm{glArch}(\gamma(u,z))$ with respect to $\nu_A$ and $\tau_A(u,z)$ in the sense of `IsOrbitalIntegralOn`: there is a weight $w : \mathrm{GL}_2(K_\infty) \to \mathbb{R}$, non-negative, measurable, of compact support, such that $\int_{Z(\mathrm{glArch}(\gamma(u,z)))} w(tx) \, d\tau_A(u,z) = 1$ for every $x$ with $f_{a,K}(x^{-1}\,\mathrm{glArch}(\gamma(u,z))\,x) \neq 0$, and $I_A(u,z) = \int f_{a,K}(x^{-1}\,\mathrm{glArch}(\gamma(u,z))\,x) \, w(x) \, d\nu_A$. Likewise, for all $u, z$ with $u \neq 1$ and every $v \in S_K$, the number $I_F(u,z,v)$ is an orbital integral of $f_{S_K}(v)$ along $\mathrm{finComponent}_v(\mathrm{glFin}(\gamma(u,z)))$ with respect to the local Haar measure `localHaar K v` and $\tau_F(u,z,v)$ in the sense of `IsOrbitalIntegral`, with the analogous non-negative, measurable, compactly supported weight normalised to total mass $1$ on the local centraliser at every point where the conjugated test function is non-zero.
--
--   This packages the standing data — a pinned archimedean Haar measure, a restricted-product factorisation of the adelic Haar integral, coherent Haar measures on the adelic, archimedean and local centralisers of the split regular semisimple elements $z\,\mathrm{diag}(u,1)$ with their own product factorisation, and the attendant archimedean and local orbital integrals — needed for the hyperbolic contribution of the $\mathrm{GL}(2)$ trace formula over a number field. It feeds the comparison statements which evaluate the hyperbolic term of the winding assembly against Satake data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_archHaarK_torusFamily_isOrbitalIntegral_centralScalar_mul_diagUnits2_of_isArchTestFactor_of_isLocalTestFn.lean

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

theorem AutomorphicForm.exists_eq_archHaarK_torusFamily_isOrbitalIntegral_centralScalar_mul_diagUnits2_of_isArchTestFactor_of_isLocalTestFn
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (cτK : ℝ) (hcτK : 0 < cτK) :
    ∃ (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K))) (cG : ℝ) (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))) (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))) (cT : ℝ) (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ) (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ),
      νA = AutomorphicForm.archHaarK K ∧ (∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.glBorelOf (InfiniteAdeleRing K)] fa νA →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localGLBorel K v] (fS v)
          (AutomorphicForm.localHaar K v)) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
              AutomorphicForm.localIntegralSet K v) →
            f g = fa (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) →
        (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∉
              AutomorphicForm.localIntegralSet K v) → f g = 0) →
          ∫ g, f g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
            cG * (∫ x, fa x ∂νA) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v)) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK)) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z)) ∧ (∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v)) ∧ (∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1) ∧ 0 < cT ∧ (∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF u z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S, WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v)) ∧
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z)) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v)) := by sorry
