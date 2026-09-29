-- Prove2me | Theorems.Thm_AutomorphicForm_exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
-- name    : AutomorphicForm.exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/43a6b25e-69af-5728-8868-1dbff228f717
-- title:
--   Uniform Haar families on split-class centralisers, one factorisation constant
-- statement:
--   Let $K$ be a number field, equip the idele units $\mathbb{A}_K^\times = (\mathrm{AdeleRing}\ \mathcal{O}_K\ K)^\times$ with their Borel $\sigma$-algebra, let $\nu$ be a Haar measure on $\mathbb{A}_K^\times$, and let $c_\tau>0$ be a real number. For $u\in K^\times$ and $z\in\mathbb{A}_K^\times$ write $\gamma(u,z)=z\cdot I_2\cdot \mathrm{diag}(u,1)$, the product of the scalar matrix attached to $z$ with the diagonal unit matrix `diagUnits2` at the idelic image of $u$ and $1$. The assertion is the existence of three families of measures and one real constant $c_T$: measures $\tau_G(u,z)$ on the centraliser of $\{\gamma(u,z)\}$ in $GL_2(\mathbb{A}_K)$ (Borel $\sigma$-algebra), measures $\tau_\infty(u,z)$ on the centraliser of the archimedean component $\mathrm{glArch}\,\gamma(u,z)$ in $GL_2(\mathbb{A}_{K,\infty})$, and, for each finite place $v$, measures $\tau_v(u,z)$ on the centraliser of the $v$-component of $\gamma(u,z)$ in $GL_2(K_v)$, all for the Borel $\sigma$-algebras, such that for all $u,z$ with $u\neq 1$ in $K$: $\tau_G(u,z)$ is a Haar measure and for every $g:GL_2(\mathbb{A}_K)\to\mathbb{C}$ one has $\int g\,d\tau_G(u,z)=c_\tau\int g(\mathrm{diag}(p_1,p_2))\,d(\nu\otimes\nu)(p)$; $\tau_\infty(u,z)$ and each $\tau_v(u,z)$ are Haar measures; $\tau_v(u,z)$ gives mass $1$ to the preimage of `localIntegralSet`, the set of matrices in $GL_2(K_v)$ whose entries and whose inverse's entries lie in the valuation ring; $c_T>0$; and, for every finite set $S$ of finite places and all $W$, $W_\infty$, $W_S$ with $W_\infty$ a.e. strongly measurable for $\tau_\infty(u,z)$, each $W_S(v)$ a.e. strongly measurable for $\tau_v(u,z)$ ($v\in S$), $W(t)=W_\infty(\mathrm{glArch}\,t)\prod_{v\in S}W_S(v)(t_v)$ whenever all components of $t$ outside $S$ are integral, and $W(t)=0$ whenever some component of $t$ outside $S$ is not integral, one has $\int W\,d\tau_G(u,z)=c_T\bigl(\int W_\infty\,d\tau_\infty(u,z)\bigr)\prod_{v\in S}\int W_S(v)\,d\tau_v(u,z)$. The same constants $c_\tau$, $c_T$ serve all $(u,z)$.
--
--   This is the measure-theoretic input for orbital integrals at regular split (hyperbolic) classes: the centraliser of such a class is the diagonal torus, canonically $\mathbb{A}_K^\times\times\mathbb{A}_K^\times$, so a single pair of normalising constants works uniformly in $(u,z)$, and the global Haar measure factorises as a restricted product of local ones with mass one on the integral points. It supplies the torus-measure package used in the evaluation of hyperbolic orbital integrals against archimedean test factors and local test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct.lean

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

theorem AutomorphicForm.exists_torusFamily_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (cτK : ℝ) (hcτK : 0 < cτK) :
    ∃ (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))) (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))) (cT : ℝ),
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure) ∧ (∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
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
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v)) := by sorry
