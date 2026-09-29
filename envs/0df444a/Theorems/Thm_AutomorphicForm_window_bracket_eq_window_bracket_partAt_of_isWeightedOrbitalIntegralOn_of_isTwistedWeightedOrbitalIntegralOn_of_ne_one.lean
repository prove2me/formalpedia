-- Prove2me | Theorems.Thm_AutomorphicForm_window_bracket_eq_window_bracket_partAt_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one
-- name    : AutomorphicForm.window_bracket_eq_window_bracket_partAt_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/82c1a6d1-2236-526b-8947-b07e9c9433aa
-- title:
--   Locality of the window bracket in the S-and-infinity coordinates
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $\nu Z_K$ be a Haar measure on the idele class group $(\mathbb{A}_K)^\times$ (as a topological group with its Borel structure), and $S_K$ a finite set of primes of $\mathcal{O}_K$. Throughout, for $u \in K^\times$ and $z \in (\mathbb{A}_K)^\times$ write $\gamma'(u,z) := \mathrm{scalar}(z)\cdot \mathrm{diag}(u,1)$ for the element [`AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) u) 1`](def/AutomorphicForm_AdelicLsXi.html#L18) of $\mathrm{GL}_2(\mathbb{A}_K)$; its archimedean component is $\mathrm{glArch}\,\gamma'(u,z)$ and its component at a finite prime $v$ is $\mathrm{finComponent}_v(\mathrm{glFin}\,\gamma'(u,z))$.
--
--   Test data over $K$: a function $f_{a,K}$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ with `hfaK`, i.e. $f_{a,K}$ is of the form $\Phi$ applied to the matrix entries read in the mixed space of $K$ for some $C^\infty$ function $\Phi$, and has compact support; and for every finite prime $v$ a function $f_{S,K}(v)$ on $\mathrm{GL}_2(K_v)$, with `hfSK` requiring for $v \in S_K$ that $f_{S,K}(v)$ be locally constant with compact support. A Borel measure $\nu_A$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ is given.
--
--   Torus measures (the hypotheses of the window-term packaging). A constant $c_{\tau K} > 0$; a family $\tau_G(u,z)$ of measures on the centraliser of $\gamma'(u,z)$ in $\mathrm{GL}_2(\mathbb{A}_K)$, which by `hτG` is Haar and by `hτGc` satisfies, for every $u$ with $u \neq 1$, every $z$ and every $g \colon \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, the identity $\int g(t)\,d\tau_G(u,z) = c_{\tau K}\int g(\mathrm{diag}(p_1,p_2))\,d(\nu Z_K \times \nu Z_K)$. A family $\tau_A(u,z)$ of measures on the centraliser of the archimedean component of $\gamma'(u,z)$, Haar for $u \neq 1$ by `hτA`; and a family $\tau_F(u,z,v)$ of measures on the local centraliser $\mathrm{Cent}(\mathrm{finComponent}_v(\mathrm{glFin}\,\gamma'(u,z)))$ in $\mathrm{GL}_2(K_v)$, Haar for $u \neq 1$ by `hτF` and of total mass $1$ on the preimage of the integral set [`AutomorphicForm.localIntegralSet K v`](def/AutomorphicForm_LocalOrbitalBase.html#L100) (those $g$ with $g$ and $g^{-1}$ having entries in $\mathcal{O}_{K_v}$) by `hτF1`.
--
--   Restricted-product factorisation. A constant $c_T > 0$ together with the hypothesis `hT`: for all $u$, $z$, every finite set $S$ of primes, and all functions $W$ on $\mathrm{GL}_2(\mathbb{A}_K)$, $W_a$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ and $W_S(v)$ on $\mathrm{GL}_2(K_v)$, if $u \neq 1$, if $W_a$ is a.e. strongly measurable for $\tau_A(u,z)$ and each $W_S(v)$ ($v \in S$) a.e. strongly measurable for $\tau_F(u,z,v)$, if $W(t) = W_a(\mathrm{glArch}\,t)\prod_{v \in S} W_S(v)(\mathrm{finComponent}_v(\mathrm{glFin}\,t))$ for every $t$ in the centraliser of $\gamma'(u,z)$ all of whose components outside $S$ lie in the local integral sets, and if $W(t) = 0$ for every such $t$ having some component outside $S$ not in the local integral set, then $\int W\,d\tau_G(u,z) = c_T\,\big(\int W_a\,d\tau_A(u,z)\big)\prod_{v \in S}\int W_S(v)\,d\tau_F(u,z,v)$.
--
--   Unweighted orbital values: functions $I_A(u,z)$ and $I_F(u,z,v)$ with `hIA` stating, for $u \neq 1$, that $I_A(u,z)$ is an orbital integral of $f_{a,K}$ at the archimedean component of $\gamma'(u,z)$ against $\nu_A$ and $\tau_A(u,z)$ — that is, there is a section function $w \geq 0$, measurable, of compact support, with $\int_{\mathrm{Cent}} w(tx)\,d\tau_A = 1$ whenever $f_{a,K}(x^{-1}\gamma x) \neq 0$, such that $I_A(u,z) = \int f_{a,K}(x^{-1}\gamma x)w(x)\,d\nu_A$ — and with `hIF` stating the analogous local statement for $f_{S,K}(v)$, $v \in S_K$, at $\mathrm{finComponent}_v(\mathrm{glFin}\,\gamma'(u,z))$ against the local Haar measure `localHaar` and $\tau_F(u,z,v)$.
--
--   Galois data: $L/K$ is Galois, $\sigma$ is an automorphism such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and $[L:K]$ is prime.
--
--   Test data over $L$: a function $\varphi_a$ on $\mathrm{GL}_2(\mathbb{A}_{L,\infty})$ which is a smooth function of the mixed-space entries with compact support (`hφa`), and functions $\varphi_S(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$ which for $v \in S_K$ are locally constant with compact support (`hφS`).
--
--   Weighted values over $K$: functions $J_A(u,z)$ and $J_F(u,z,v)$, where `hJA` asserts for $u \neq 1$ that $J_A(u,z)$ is the weighted orbital integral of $f_{a,K}$ at the archimedean component of $\gamma'(u,z)$ against $\nu_A$, $\tau_A(u,z)$ and the weight
--   $$y \mapsto -\log \mathrm{archHeight}_K(y) - \log \mathrm{archHeight}_K\big(\mathrm{glArch}(\mathrm{adelicWeyl}_K)\cdot y\big),$$
--   $\mathrm{archHeight}_K(g)$ being the product over infinite places of the local heights $\lVert\det\rVert/\mathrm{rowNormSq}$ raised to the multiplicity of the place, and $\mathrm{adelicWeyl}_K$ the image of the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$; that is, $J_A(u,z) = \int f_{a,K}(x^{-1}\gamma x)\,\mathrm{wt}(x)\,s(x)\,d\nu_A$ for some section function $s$ as above. Correspondingly `hJF` asserts for $v \in S_K$ that $J_F(u,z,v)$ is the local weighted orbital integral of $f_{S,K}(v)$ at $\mathrm{finComponent}_v(\mathrm{glFin}\,\gamma'(u,z))$ against `localHaar` and $\tau_F(u,z,v)$ with the local weight `LocalWeight.weight`.
--
--   Normalisation of the archimedean measures: a Borel measure $\nu_A'$ on $\mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$, with `hνA` fixing $\nu_A =$ [`AutomorphicForm.archHaarK K`](def/AutomorphicForm_TwistedOrbital.html#L401) and `hνA'` fixing $\nu_A' =$ [`AutomorphicForm.archHaarL K L`](def/AutomorphicForm_TwistedOrbital.html#L412), the Haar measures on these two groups.
--
--   Norm lifts and twisted torus measures: a family $\delta_A(u,z) \in \mathrm{GL}_2(L \otimes_K \mathbb{A}_{K,\infty})$ with `hδA` requiring, for $u \neq 1$ and whenever the archimedean component of $\gamma'(u,z)$ is a $\sigma$-norm (i.e. some $\delta$ has $\mathrm{toTensorGL}(\gamma)$ conjugate to $\prod_{i<[L:K]}\sigma^i\delta$), that the norm string $\prod_{i<[L:K]}\sigma^i\big(\delta_A(u,z)\big)$ equals $\mathrm{toTensorGL}$ of that archimedean component; a family $\tau_A'(u,z)$ of measures on the $\sigma$-twisted centraliser $\{t : t\,\delta_A(u,z)\,(\sigma t)^{-1} = \delta_A(u,z)\}$, Haar for $u \neq 1$ (`hτA'`) and, under the same norm hypothesis, coupled to $\tau_A(u,z)$ with conjugator $1$ (`hτA'c`): the pushforward of $\tau_A'(u,z)$ along the inclusion of the twisted centraliser equals the pushforward of $\tau_A(u,z)$ along $\mathrm{toTensorGL}$. Likewise a family $\delta_F(u,z,v) \in \mathrm{GL}_2(L \otimes_K K_v)$ with `hδF` (for $u \neq 1$, $v \in S_K$ and the local component a $\sigma$-norm, the norm string of $\delta_F(u,z,v)$ equals $\mathrm{toTensorGL}$ of that component) and measures $\tau_F'(u,z,v)$ on the corresponding twisted centralisers, Haar for $u \neq 1$ (`hτF'`) and of mass $1$ on the preimage of [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) (`hτF'1`).
--
--   Twisted weighted values: functions $J_A'(u,z)$ and $J_F'(u,z,v)$. By `hJA'`, for $u \neq 1$ and when the archimedean component of $\gamma'(u,z)$ is a $\sigma$-norm, $J_A'(u,z)$ is the twisted weighted orbital integral of $\varphi_a \circ \mathrm{archIdentGL}$ at $\delta_A(u,z)$ against $\nu_A'$, $\tau_A'(u,z)$ and the weight
--   $$y \mapsto -\log \mathrm{archHeight}_L(\mathrm{archIdentGL}\,y) - \log \mathrm{archHeight}_L\big(\mathrm{glArch}(\mathrm{adelicWeyl}_L)\cdot \mathrm{archIdentGL}\,y\big),$$
--   that is, $J_A'(u,z) = \int \varphi_a(\mathrm{archIdentGL}(x^{-1}\delta_A(u,z)\,\sigma x))\,\mathrm{wt}(x)\,s(x)\,d\nu_A'$ for a twisted section function $s$ (non-negative, measurable, compactly supported, with $\int w(tx)$ over the twisted centraliser equal to $1$ where the integrand does not vanish); by `hJA'0`, $J_A'(u,z) = 0$ when $u \neq 1$ and that component is not a $\sigma$-norm. By `hJF'`, for $u \neq 1$, $v \in S_K$ and the local component a $\sigma$-norm, $J_F'(u,z,v)$ is the twisted weighted orbital integral of $\varphi_S(v)$ at $\delta_F(u,z,v)$ against the semilocal Haar measure, $\tau_F'(u,z,v)$ and the semilocal weight $\sum_{w \mid v} \mathrm{weight}$; by `hJF'0` it is $0$ when the local component is not a $\sigma$-norm.
--
--   Finally, let $u \in K^\times$ with $u \neq 1$ as an element of $K$, and let $w \in (\mathbb{A}_K)^\times$. Writing $\ell := [L:K]$ viewed in $\mathbb{C}$ and $w_{S} :=$ [`NumberField.Idele.partAt K SK w`](def/NumberField_IdeleProductMeasure.html#L90) for the idele with the archimedean part of $w$ unchanged and finite part the truncation `truncFin` of that of $w$ at $S_K$, the conclusion is the single equality of complex numbers
--   $$\big(J_A'(u,w) - \ell\,J_A(u,w)\big)\prod_{v \in S_K} I_F(u,w,v) + I_A(u,w)\sum_{v \in S_K}\big(J_F'(u,w,v) - \ell\,J_F(u,w,v)\big)\prod_{v' \in S_K \setminus \{v\}} I_F(u,w,v')$$
--   $$= \big(J_A'(u,w_S) - \ell\,J_A(u,w_S)\big)\prod_{v \in S_K} I_F(u,w_S,v) + I_A(u,w_S)\sum_{v \in S_K}\big(J_F'(u,w_S,v) - \ell\,J_F(u,w_S,v)\big)\prod_{v' \in S_K \setminus \{v\}} I_F(u,w_S,v'),$$
--   the inner products being over $S_K$ with $v$ erased.
--
--   The bracket appearing here is the window, or discrepancy, term attached to the split regular classes $z\,\mathrm{diag}(u,1)$ in the comparison of the weighted trace formula for $\mathrm{GL}_2/K$ with the $\sigma$-twisted weighted trace formula for $\mathrm{GL}_2/L$; the statement says that its value depends on the central idele only through the components at $S_K$ and at the infinite places. It is used in this form by [`AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_window_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_ne_one_unweighted`](thm.html#AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_window_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_ne_one_unweighted), where the centre integral over the idele class group is unfolded and the surgery idele is returned to its $S_K$-part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_window_bracket_eq_window_bracket_partAt_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in

theorem AutomorphicForm.window_bracket_eq_window_bracket_partAt_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))

    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))

    (cτK : ℝ) (hcτK : 0 < cτK)
    (τG : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τG u z).IsHaarMeasure)
    (hτGc : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG u z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA u z))
    (τF : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF u z v))
    (hτF1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF u z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (S : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        (u : K) ≠ 1 →
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
          ∫ t, W t ∂(τG u z) = cT * (∫ t, Wa t ∂(τA u z)) * ∏ v ∈ S, ∫ t, WS v t ∂(τF u z v))

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))

    [IsGalois K L] (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hprime : (Module.finrank K L).Prime)

    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφS : ∀ v ∈ SK, AutomorphicForm.IsSemiLocalTestFn K L v (φS v))

    (JA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsWeightedOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (fun y : GL (Fin 2) (InfiniteAdeleRing K) =>
        -Real.log (AutomorphicForm.WindowedSiegel.archHeight K y)
          - Real.log (AutomorphicForm.WindowedSiegel.archHeight K
              (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) * y)))
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (JA u z))
    (JF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsWeightedOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (JF u z v))

    (νA' : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hνA : νA = AutomorphicForm.archHaarK K) (hνA' : νA' = AutomorphicForm.archHaarL K L)
    (δA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.normString K L (InfiniteAdeleRing K) σ (δA u z) =
        AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))
    (τA' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ),
      Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ (δA u z)))
    (hτA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (τA' u z).IsHaarMeasure)
    (hτA'c : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.Coupled K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (δA u z) 1 (τA u z) (τA' u z))
    (δF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.normString K L (v.adicCompletion K) σ (δF u z v) =
        AutomorphicForm.toTensorGL K L (v.adicCompletion K) (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (τF' : ∀ (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (δF u z v)))
    (hτF' : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → (τF' u z v).IsHaarMeasure)
    (hτF'1 : ∀ u z v, ((u : Kˣ) : K) ≠ 1 → τF' u z v (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1)
    (JA' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hJA' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ νA'
        (fun y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
          -Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
            - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
                (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
                  AutomorphicForm.archIdentGL K L y)))
        (δA u z) (τA' u z) (φa ∘ AutomorphicForm.archIdentGL K L) (JA' u z))
    (hJA'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → (¬ ∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) → JA' u z = 0)
    (JF' : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hJF' : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (δF u z v) (τF' u z v) (φS v) (JF' u z v))
    (hJF'0 : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, (¬ ∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) →
      JF' u z v = 0)
    (u : Kˣ) (hu1 : (u : K) ≠ 1) (w : (AdeleRing (𝓞 K) K)ˣ) :
    ((JA' u w - (Module.finrank K L : ℂ) * JA u w) * ∏ v ∈ SK, IF u w v +
        IA u w * ∑ v ∈ SK, (JF' u w v - (Module.finrank K L : ℂ) * JF u w v) * ∏ v' ∈ SK.erase v, IF u w v') =
      ((JA' u (NumberField.Idele.partAt K SK w) - (Module.finrank K L : ℂ) * JA u (NumberField.Idele.partAt K SK w)) * ∏ v ∈ SK, IF u (NumberField.Idele.partAt K SK w) v +
        IA u (NumberField.Idele.partAt K SK w) * ∑ v ∈ SK, (JF' u (NumberField.Idele.partAt K SK w) v - (Module.finrank K L : ℂ) * JF u (NumberField.Idele.partAt K SK w) v) * ∏ v' ∈ SK.erase v, IF u (NumberField.Idele.partAt K SK w) v') := by sorry
