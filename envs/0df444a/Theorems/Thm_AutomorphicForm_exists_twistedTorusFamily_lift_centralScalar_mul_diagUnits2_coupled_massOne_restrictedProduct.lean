-- Prove2me | Theorems.Thm_AutomorphicForm_exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
-- name    : AutomorphicForm.exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/031d71db-1df3-5b7b-8ff1-3b1cfbb9aff8
-- title:
--   Twisted torus family along lifts of a split hyperbolic family
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ finite Galois, $\sigma \in \mathrm{Gal}(L/K)$ is an automorphism such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$, and $\sigma^{[L:K]} = 1$. Write $\mathbb{A} = \mathbb{A}_K$ for the adele ring of $K$ (adeles of $\mathcal{O}_K$ in $K$), $\mathbb{A}_\infty$ for the infinite adele ring, and $K_v$ for the completion at a height-one prime $v$ of $\mathcal{O}_K$. All the groups $\mathrm{GL}_2$ occurring, and the centralisers and twisted centralisers of their elements, carry their Borel $\sigma$-algebras; $\mathbb{A}^\times$ is given a Borel measurable structure and a Haar measure $\nu_{Z_K}$, and $c_{\tau,K} > 0$, $c_T > 0$ are real constants.
--
--   For $u \in K^\times$ and $z \in \mathbb{A}^\times$ put $\gamma(u,z) =$ `centralScalar` $z \cdot$ `diagUnits2` $(u)\,1$, that is the scalar matrix $z \cdot I$ times the diagonal matrix with entries the image of $u$ in $\mathbb{A}$ and $1$, so $\gamma(u,z) = \mathrm{diag}(zu, z) \in \mathrm{GL}_2(\mathbb{A})$. Its archimedean component is `AdelicLevel.glArch` $\gamma(u,z)$, obtained by applying the projection $\mathbb{A} \to \mathbb{A}_\infty$ entrywise, and its component at $v$ is `AdelicLevel.finComponent` $v$ applied to `AdelicLevel.glFin` $\gamma(u,z)$, obtained by applying $\mathbb{A} \to \widehat{\mathbb{A}} \to K_v$ entrywise.
--
--   The data on the ground (untwisted) side consist of a family $\tau_G(u,z)$ of measures on the centraliser of $\{\gamma(u,z)\}$ in $\mathrm{GL}_2(\mathbb{A})$, a family $\tau_A(u,z)$ of measures on the centraliser of the archimedean component in $\mathrm{GL}_2(\mathbb{A}_\infty)$, and a family $\tau_F(u,z,v)$ of measures on the centraliser of the component at $v$ in $\mathrm{GL}_2(K_v)$. These are subject to the following hypotheses, all of them imposed for those pairs $(u,z)$ with the image of $u$ in $K$ different from $1$: $\tau_G(u,z)$ is a Haar measure (`hτG`); $\tau_G(u,z)$ unfolds against the split torus, in the sense that for every $g : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ one has $\int g(t)\, d\tau_G(u,z) = c_{\tau,K} \int g(\mathrm{diag}(p_1,p_2))\, d(\nu_{Z_K} \otimes \nu_{Z_K})$ (`hτGc`); $\tau_A(u,z)$ is a Haar measure (`hτA`); each $\tau_F(u,z,v)$ is a Haar measure (`hτF`); each $\tau_F(u,z,v)$ gives mass $1$ to the set of elements of the centraliser lying in [`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100) $K\,v$, the set of $g \in \mathrm{GL}_2(K_v)$ for which both $g$ and $g^{-1}$ have all entries in the ring of integers of $K_v$ (`hτF1`); and the restricted-product identity `hT` holds: for every finite set $S$ of height-one primes and all functions $W$ on $\mathrm{GL}_2(\mathbb{A})$, $W_\infty$ on $\mathrm{GL}_2(\mathbb{A}_\infty)$ and $W_v$ on $\mathrm{GL}_2(K_v)$ for each $v$, such that $W_\infty$ is almost everywhere strongly measurable for $\tau_A(u,z)$, each $W_v$ with $v \in S$ is almost everywhere strongly measurable for $\tau_F(u,z,v)$, $W(t) = W_\infty(t_\infty) \prod_{v \in S} W_v(t_v)$ for every $t$ in the centraliser all of whose components outside $S$ are integral in the above sense, and $W(t) = 0$ whenever some component of $t$ outside $S$ fails to be integral, one has $\int W \, d\tau_G(u,z) = c_T \,\bigl(\int W_\infty \, d\tau_A(u,z)\bigr) \prod_{v \in S} \int W_v \, d\tau_F(u,z,v)$.
--
--   The assertion is the existence of a family of lifts $\delta : K^\times \to \mathbb{A}^\times \to \mathrm{GL}_2(L \otimes_K \mathbb{A})$ together with families of measures $\tau'_G(u,z)$ on the $\sigma$-twisted centraliser of $\delta(u,z)$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A})$, $\tau'_A(u,z)$ on the $\sigma$-twisted centraliser of `tensorArch` $\delta(u,z)$ in $\mathrm{GL}_2(L \otimes_K \mathbb{A}_\infty)$, and $\tau'_F(u,z,v)$ on the $\sigma$-twisted centraliser of `tensorPlace` $v$ $\delta(u,z)$ in $\mathrm{GL}_2(L \otimes_K K_v)$. Here the twisted centraliser of $\delta$ is the subgroup of $t$ with $t\,\delta\,(\sigma t)^{-1} = \delta$, where $\sigma$ acts on $\mathrm{GL}_2(L \otimes_K A)$ entrywise through $\sigma \otimes \mathrm{id}$; `tensorArch` and `tensorPlace` $v$ are induced entrywise by $\mathrm{id}_L \otimes (\mathbb{A} \to \mathbb{A}_\infty)$ and $\mathrm{id}_L \otimes (\mathbb{A} \to K_v)$; `normString` $\sigma\,\delta$ is the product $\delta \cdot \sigma(\delta) \cdots \sigma^{[L:K]-1}(\delta)$ of the first $[L:K]$ iterates; `toTensorGL` is induced entrywise by $a \mapsto 1 \otimes a$; and `IsNormOf` $\gamma\,\delta_0$ means that there is $y$ with `toTensorGL` $\gamma = y^{-1} \cdot$ `normString` $\sigma\,\delta_0 \cdot y$.
--
--   The twelve conclusions, each asserted for all $(u,z)$ (and all $v$ where relevant) with the image of $u$ in $K$ different from $1$, are as follows.
--
--   (i) If $\gamma(u,z)$ is a norm, i.e. there exists $\delta_0$ with `IsNormOf` $K\,L\,\mathbb{A}\,\sigma\,\gamma(u,z)\,\delta_0$, then the lift is exact: `normString` $\sigma\,(\delta(u,z)) =$ `toTensorGL` $\gamma(u,z)$.
--
--   (ii) If the archimedean component of $\gamma(u,z)$ is a norm over $\mathbb{A}_\infty$, then `normString` $\sigma$ of `tensorArch` $\delta(u,z)$ equals `toTensorGL` of that archimedean component.
--
--   (iii) If the component of $\gamma(u,z)$ at $v$ is a norm over $K_v$, then `normString` $\sigma$ of `tensorPlace` $v\,\delta(u,z)$ equals `toTensorGL` of that component.
--
--   (iv) If $\gamma(u,z)$ is a norm, then $\tau'_G(u,z)$ is a Haar measure on the twisted centraliser of $\delta(u,z)$.
--
--   (v) If $\gamma(u,z)$ is a norm, then $\tau'_G(u,z)$ unfolds with the same constant: for every $g : \mathrm{GL}_2(L \otimes_K \mathbb{A}) \to \mathbb{C}$, $\int g(s)\, d\tau'_G(u,z) = c_{\tau,K} \int g\bigl(\mathrm{toTensorGL}(\mathrm{diag}(p_1,p_2))\bigr)\, d(\nu_{Z_K} \otimes \nu_{Z_K})$.
--
--   (vi) If $\gamma(u,z)$ is a norm, then $\tau_G(u,z)$ and $\tau'_G(u,z)$ are coupled with conjugator $1$: the pushforward of $\tau'_G(u,z)$ under $t \mapsto 1^{-1} t 1$ equals the pushforward of $\tau_G(u,z)$ under $t \mapsto$ `toTensorGL` $t$, as measures on $\mathrm{GL}_2(L \otimes_K \mathbb{A})$.
--
--   (vii) $\tau'_A(u,z)$ is a Haar measure on the twisted centraliser of `tensorArch` $\delta(u,z)$; no norm hypothesis is required.
--
--   (viii) If the archimedean component of $\gamma(u,z)$ is a norm, then $\tau_A(u,z)$ and $\tau'_A(u,z)$ are coupled with conjugator $1$ relative to that component and the lift `tensorArch` $\delta(u,z)$.
--
--   (ix) For every $v$, $\tau'_F(u,z,v)$ is a Haar measure on the twisted centraliser of `tensorPlace` $v\,\delta(u,z)$; no norm hypothesis is required.
--
--   (x) For every $v$, $\tau'_F(u,z,v)$ gives mass $1$ to the set of elements of that twisted centraliser lying in [`AutomorphicForm.semiLocalIntegralSet`](def/AutomorphicForm_TwistedOrbital.html#L136) $K\,L\,v$, the set of $g \in \mathrm{GL}_2(L \otimes_K K_v)$ for which both $g$ and $g^{-1}$ have all entries in the image of the semi-local integers of $L$ over $v$.
--
--   (xi) If the component of $\gamma(u,z)$ at $v$ is a norm over $K_v$, then $\tau_F(u,z,v)$ and $\tau'_F(u,z,v)$ are coupled with conjugator $1$ relative to that component and the lift `tensorPlace` $v\,\delta(u,z)$.
--
--   (xii) If $\gamma(u,z)$ is a norm, the twisted restricted-product identity holds with the same constant $c_T$: for every finite set $S$ of height-one primes and all functions $W$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A})$, $W_\infty$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_\infty)$ and $W_v$ on $\mathrm{GL}_2(L \otimes_K K_v)$, such that $W_\infty$ is almost everywhere strongly measurable for $\tau'_A(u,z)$, each $W_v$ with $v \in S$ is almost everywhere strongly measurable for $\tau'_F(u,z,v)$, one has $W(t) = W_\infty(\mathrm{tensorArch}\, t) \prod_{v \in S} W_v(\mathrm{tensorPlace}\, v\, t)$ for every $t$ in the twisted centraliser of $\delta(u,z)$ all of whose components outside $S$ lie in the semi-local integral set, and $W(t) = 0$ whenever some component of $t$ outside $S$ does not, then $\int W \, d\tau'_G(u,z) = c_T \,\bigl(\int W_\infty \, d\tau'_A(u,z)\bigr) \prod_{v \in S} \int W_v \, d\tau'_F(u,z,v)$.
--
--   This is the transport of a torus measure family along the split hyperbolic classes $\mathrm{diag}(zu,z)$ from the group over $K$ to the $\sigma$-twisted side over $L \otimes_K \mathbb{A}_K$, in the cyclic base-change comparison of trace formulae for $\mathrm{GL}_2$: exact lifts of regular diagonal norm classes are produced, and the twisted Haar measures are normalised so that the unfolding constant $c_{\tau,K}$, the local mass-one normalisation and the restricted-product constant $c_T$ are the same on both sides. It feeds the comparison of hyperbolic terms, being used in the derivation of the identity between the winding datum of the hyperbolic intercept and the Satake–Laurent expansion of the eigensystem coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_twistedTorusFamily_lift_centralScalar_mul_diagUnits2_coupled_massOne_restrictedProduct
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hσ : σ ^ Module.finrank K L = 1)
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (cτK : ℝ) (hcτK : 0 < cτK)
    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))))) (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))) (cT : ℝ)
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v)) :
    ∃ (δ : Kˣ → (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K))
      (τG' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), @Measure (AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δ u z)) (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ (δ u z)))
      (τA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (δ u z))) (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (δ u z))))
      (τF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)), @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (δ u z))) (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (δ u z)))),

      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) →
        AutomorphicForm.normString K L (AdeleRing (𝓞 K) K) σ (δ u z) =
          AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) ∧
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀) →
        AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (δ u z)) =
          AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) ∧
      (∀ u z v, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀) →
        AutomorphicForm.normString K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (δ u z)) =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K)
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) ∧

      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) → @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (AdeleRing (𝓞 K) K) σ (δ u z)) (τG' u z)) ∧
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) → ∀ g : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ,
        ∫ s : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δ u z), g (s : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K)) ∂(τG' u z) =
          cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ,
            g (AutomorphicForm.toTensorGL K L (AdeleRing (𝓞 K) K) (diagUnits2 p.1 p.2)) ∂(νZK.prod νZK)) ∧
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) →
        AutomorphicForm.Coupled K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) (δ u z) 1 (τG u z) (τG' u z)) ∧

      (∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ (AutomorphicForm.tensorArch K L (δ u z))) (τA' u z)) ∧
      (∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ₀) →
        AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))
          (AutomorphicForm.tensorArch K L (δ u z)) 1 (τA u z) (τA' u z)) ∧

      (∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (AutomorphicForm.tensorPlace K L v (δ u z))) (τF' u z v)) ∧
      (∀ u z v, ((u : Kˣ) : K) ≠ 1 →
        τF' u z v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1) ∧
      (∀ u z v, ((u : Kˣ) : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ₀) →
        AutomorphicForm.Coupled K L (v.adicCompletion K) σ
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
          (AutomorphicForm.tensorPlace K L v (δ u z)) 1 (τF u z v) (τF' u z v)) ∧

      (∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ), (u : K) ≠ 1 → (∃ δ₀, AutomorphicForm.IsNormOf K L (AdeleRing (𝓞 K) K) σ (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) δ₀) → ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (L ⊗[K] AdeleRing (𝓞 K) K) → ℂ)
        (Wa : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ
          (AutomorphicForm.tensorArch K L (δ u z))] (fun t => Wa t) (τA' u z) →
        (∀ v ∈ S, AEStronglyMeasurable[AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ
          (AutomorphicForm.tensorPlace K L v (δ u z))] (fun t => WS v t) (τF' u z v)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δ u z),
          (∀ v ∉ S, AutomorphicForm.tensorPlace K L v t ∈ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = Wa (AutomorphicForm.tensorArch K L t) *
              ∏ v ∈ S, WS v (AutomorphicForm.tensorPlace K L v t)) →
        (∀ t : AutomorphicForm.twistedCentralizer K L (AdeleRing (𝓞 K) K) σ (δ u z),
          (∃ v ∉ S, AutomorphicForm.tensorPlace K L v t ∉ AutomorphicForm.semiLocalIntegralSet K L v) →
            W t = 0) →
          ∫ t, W t ∂(τG' u z) = cT * (∫ t, Wa t ∂(τA' u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF' u z v)) := by sorry
