-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_mul_window_bracket_sPart_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one
-- name    : AutomorphicForm.integrable_mul_window_bracket_sPart_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/7bcdf60b-e3eb-5fee-86c5-ed27f60e6e1d
-- title:
--   Integrability of the window bracket against the S-part measure
-- statement:
--   Setting. $K$ and $L$ are number fields with $L$ a $K$-algebra; the idele group $(\mathbb{A}_K)^\times$ carries a measurable structure which is the Borel structure of its topology, and $\nu_{Z,K}$ (`νZK`) is a Haar measure on it. The group $\mathrm{GL}_2$ over the adeles, over the infinite adeles, over a completion $K_v$, over $L\otimes_K K_\infty$ and over $L\otimes_K K_v$, and all centralisers and $\sigma$-twisted centralisers occurring below, carry the Borel structures of their topologies (`glBorel`, `glBorelOf`, `centralizerBorel`, `localCentralizerBorel`, `twistedCentralizerBorel`). Further data: a group homomorphism $\xi$ from the full subgroup $\top \le (\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$ such that the associated complex-valued function $z \mapsto \xi(z)$ is continuous (`hξc`), and a finite set $S_K$ (`SK`) of height-one primes of $\mathcal{O}_K$.
--
--   Test functions on the $K$-side. A function $f_{a,K}$ (`faK`) on $\mathrm{GL}_2(K_\infty)$ with `hfaK` asserting that it is an archimedean test factor, i.e. there is a $C^\infty$ function $\Phi$ on matrices over the mixed space of $K$ with $f_{a,K}(g)=\Phi(\mathrm{archEntries}\,g)$ for all $g$, and $f_{a,K}$ has compact support. For every finite place $v$ a function $f_{S,K}(v)$ (`fSK`) on $\mathrm{GL}_2(K_v)$, required by `hfSK` for $v\in S_K$ to be locally constant with compact support. A measure $\nu_A$ (`νA`) on $\mathrm{GL}_2(K_\infty)$.
--
--   The hyperbolic family and its global torus measures. For $u\in K^\times$ and $z\in(\mathbb{A}_K)^\times$ write $\gamma(u,z)$ for the element $\mathrm{centralScalar}(z)\cdot \mathrm{diagUnits2}(u_{\mathbb{A}},1)=\mathrm{diag}(zu,z)$ of $\mathrm{GL}_2(\mathbb{A}_K)$, $u_{\mathbb{A}}$ being the image of $u$ under the structure map $K\to\mathbb{A}_K$. For each pair $(u,z)$ a measure $\tau_G(u,z)$ (`τG`) on the centraliser of $\{\gamma(u,z)\}$ in $\mathrm{GL}_2(\mathbb{A}_K)$ is given; `hτG` requires it to be Haar whenever $u\ne 1$ in $K$, and `hτGc`, with a constant $c_{\tau,K}>0$ (`cτK`, `hcτK`), requires that for $u\ne 1$ and every $g$ on $\mathrm{GL}_2(\mathbb{A}_K)$ one has $\int_{Z(\gamma(u,z))} g(t)\,d\tau_G(u,z) = c_{\tau,K}\int g(\mathrm{diag}(p_1,p_2))\,d(\nu_{Z,K}\otimes\nu_{Z,K})$.
--
--   Archimedean and local torus measures. Measures $\tau_A(u,z)$ (`τA`) on the centraliser of the archimedean component $\mathrm{glArch}\,\gamma(u,z)$ in $\mathrm{GL}_2(K_\infty)$, Haar for $u\ne 1$ (`hτA`); measures $\tau_F(u,z,v)$ (`τF`) on the local centraliser of the $v$-component $\mathrm{finComponent}_v(\mathrm{glFin}\,\gamma(u,z))$ in $\mathrm{GL}_2(K_v)$, Haar for $u\ne 1$ (`hτF`) and of total mass $1$ on the preimage of the integral set $\mathrm{localIntegralSet}\,K\,v$ (matrices whose entries and whose inverse's entries lie in $\mathcal{O}_v$) for $u\ne 1$ (`hτF1`).
--
--   The restricted-product splitting hypothesis. A constant $c_T>0$ (`cT`, `hcT`) and `hT`: for all $u$, $z$, every finite set $S$ of finite places, every $W$ on $\mathrm{GL}_2(\mathbb{A}_K)$, $W_a$ on $\mathrm{GL}_2(K_\infty)$ and family $W_S$, assuming $u\ne1$ in $K$, that $W_a$ is almost everywhere strongly measurable for $\tau_A(u,z)$, that $W_S(v)$ is almost everywhere strongly measurable for $\tau_F(u,z,v)$ for $v\in S$, that $W(t)=W_a(\mathrm{glArch}\,t)\prod_{v\in S}W_S(v)(\mathrm{finComponent}_v(\mathrm{glFin}\,t))$ for every $t$ in the centraliser of $\gamma(u,z)$ all of whose components outside $S$ lie in the local integral sets, and that $W(t)=0$ for every such $t$ having some component outside $S$ not in the local integral set, then $\int W\,d\tau_G(u,z) = c_T\,\bigl(\int W_a\,d\tau_A(u,z)\bigr)\prod_{v\in S}\int W_S(v)\,d\tau_F(u,z,v)$.
--
--   Product-measure data. A term $P_Z$ (`PZ`) of [`UnramifiedWhittaker.ProductMeasureData SK νZK`](def/UnramifiedWhittaker_ZetaIntegrand.html#L20), consisting of a constant $P_Z.c>0$, a measure $P_Z.\nu_S$ on $(\mathbb{A}_K)^\times$, an endomorphism $P_Z.\mathrm{projS}$ of $(\mathbb{A}_K)^\times$, a family of integer-valued functions $P_Z.\mathrm{ord}$, together with the structure's clauses `projS_off`, `decomp`, `tonelli` and `measurableSet` (summarised here: triviality of $P_Z.\mathrm{projS}$ off $S_K$, a decomposition of unit ideles outside $S_K\cup L$ into $S_K$-part, uniformizer powers and a unit idele, a Fubini formula with constant $P_Z.c$ for functions of the form $a\mapsto f(P_Z.\mathrm{projS}\,a)\prod_{v\in L}\varphi_v(P_Z.\mathrm{ord}_v a)$, and measurability of the relevant subgroups). In addition `hPo` identifies $P_Z.\mathrm{ord}$ with [`NumberField.Idele.ord K`](def/NumberField_IdeleProductMeasure.html#L13), `hPp` identifies $P_Z.\mathrm{projS}$ with the $S_K$-part map [`NumberField.Idele.partAt K SK`](def/NumberField_IdeleProductMeasure.html#L90), and `hPν` states that $\mathrm{ofReal}(P_Z.c)\cdot P_Z.\nu_S$ is the image of the restriction of $\nu_{Z,K}$ to the unit ideles outside $S_K$ under that $S_K$-part map.
--
--   Plain orbital-integral values. Complex numbers $I_A(u,z)$ (`IA`) with `hIA`: for $u\ne1$, $I_A(u,z)$ is an orbital integral on $\mathrm{GL}_2(K_\infty)$ for $\nu_A$ at $\mathrm{glArch}\,\gamma(u,z)$ with torus measure $\tau_A(u,z)$ and test function $f_{a,K}$, that is, there is a non-negative measurable compactly supported $w$ with $\int w(tx)\,d\tau_A(u,z)=1$ whenever $f_{a,K}(x^{-1}\gamma x)\ne0$ and $I_A(u,z)=\int f_{a,K}(x^{-1}\mathrm{glArch}\,\gamma(u,z)\,x)\,w(x)\,d\nu_A$. Complex numbers $I_F(u,z,v)$ (`IF`) with `hIF`: for $u\ne1$ and $v\in S_K$, the analogous local orbital integral at $\mathrm{finComponent}_v(\mathrm{glFin}\,\gamma(u,z))$ with measure $\tau_F(u,z,v)$, test function $f_{S,K}(v)$, taken against the local Haar measure $\mathrm{localHaar}\,K\,v$.
--
--   The cyclic extension. $L/K$ is Galois, $\sigma$ is an automorphism generating the Galois group in the sense that every $\tau\in\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (`hgen`), and $\ell=\mathrm{finrank}_K L$ is prime (`hprime`).
--
--   Test functions on the $L$-side. A function $\varphi_a$ (`φa`) on $\mathrm{GL}_2(L_\infty)$ that is an archimedean test factor for $L$ (`hφa`), and functions $\varphi_S(v)$ (`φS`) on $\mathrm{GL}_2(L\otimes_K K_v)$ which for $v\in S_K$ are locally constant with compact support (`hφS`).
--
--   Weighted values on the $K$-side. Complex numbers $J_A(u,z)$ (`JA`) with `hJA`: for $u\ne 1$, $J_A(u,z)$ is a weighted orbital integral on $\mathrm{GL}_2(K_\infty)$ for $\nu_A$, at $\mathrm{glArch}\,\gamma(u,z)$, with torus measure $\tau_A(u,z)$, test function $f_{a,K}$ and weight $y\mapsto -\log \mathrm{archHeight}_K(y)-\log \mathrm{archHeight}_K(\mathrm{glArch}(\mathrm{adelicWeyl})\cdot y)$, where $\mathrm{archHeight}_K(g)=\prod_{v\mid\infty}\bigl(|\det g_v|/\mathrm{rowNormSq}(g_v)\bigr)^{\mathrm{mult}(v)}$ and $\mathrm{adelicWeyl}$ is the image of the $2\times2$ antidiagonal Weyl element; that is, there is a section function $s$ as above with $J_A(u,z)=\int f_{a,K}(x^{-1}\gamma x)\,\mathrm{wt}(x)\,s(x)\,d\nu_A$. Complex numbers $J_F(u,z,v)$ (`JF`) with `hJF`: for $u\ne1$ and $v\in S_K$, the corresponding local weighted orbital integral against $\mathrm{localHaar}\,K\,v$ with the local weight $x\mapsto 2\log\bigl(\max(\|x_{00}\|,\|x_{01}\|)\cdot\mathrm{rowMaxNorm}(x)/\|\det x\|\bigr)$.
--
--   Twisted data on the $L$-side. A measure $\nu_A'$ (`νA'`) on $\mathrm{GL}_2(L\otimes_K K_\infty)$, together with `hνA` and `hνA'` identifying $\nu_A$ with [`AutomorphicForm.archHaarK K`](def/AutomorphicForm_TwistedOrbital.html#L401) and $\nu_A'$ with [`AutomorphicForm.archHaarL K L`](def/AutomorphicForm_TwistedOrbital.html#L412). Elements $\delta_A(u,z)$ (`δA`) of $\mathrm{GL}_2(L\otimes_K K_\infty)$ with `hδA`: for $u\ne1$, if $\mathrm{glArch}\,\gamma(u,z)$ is a norm (i.e. some $\delta$ satisfies $\mathrm{toTensorGL}(\mathrm{glArch}\,\gamma(u,z))=y^{-1}\,\mathrm{normString}_\sigma(\delta)\,y$ for some $y$, where $\mathrm{normString}_\sigma(\delta)=\prod_{i<\ell}\sigma^i_{\mathrm{GL}}(\delta)$), then $\mathrm{normString}_\sigma(\delta_A(u,z))=\mathrm{toTensorGL}(\mathrm{glArch}\,\gamma(u,z))$. Measures $\tau_A'(u,z)$ (`τA'`) on the $\sigma$-twisted centraliser $\{t: t\,\delta_A(u,z)\,\sigma_{\mathrm{GL}}(t)^{-1}=\delta_A(u,z)\}$, Haar for $u\ne1$ (`hτA'`), and `hτA'c`: for $u\ne1$ and under the same norm hypothesis, $\tau_A(u,z)$ and $\tau_A'(u,z)$ are coupled with conjugator $1$, i.e. the image of $\tau_A'(u,z)$ under $t\mapsto 1^{-1}t\,1$ equals the image of $\tau_A(u,z)$ under $\mathrm{toTensorGL}$. Elements $\delta_F(u,z,v)$ (`δF`) of $\mathrm{GL}_2(L\otimes_K K_v)$ with the analogous norm-string identity `hδF` for $v\in S_K$, and measures $\tau_F'(u,z,v)$ (`τF'`) on the corresponding twisted centralisers, Haar (`hτF'`) and of mass $1$ on the preimage of the semi-local integral set $\mathrm{semiLocalIntegralSet}\,K\,L\,v$ (`hτF'1`) for $u\ne1$.
--
--   Twisted weighted values. Complex numbers $J_A'(u,z)$ (`JA'`) with `hJA'`: for $u\ne1$ and under the norm hypothesis at the archimedean place, $J_A'(u,z)$ is a twisted weighted orbital integral on $\mathrm{GL}_2(L\otimes_K K_\infty)$ for $\nu_A'$ at $\delta_A(u,z)$, with twisted torus measure $\tau_A'(u,z)$, test function $\varphi_a\circ \mathrm{archIdentGL}$ and weight $y\mapsto -\log\mathrm{archHeight}_L(\mathrm{archIdentGL}\,y)-\log\mathrm{archHeight}_L(\mathrm{glArch}(\mathrm{adelicWeyl}_L)\cdot \mathrm{archIdentGL}\,y)$, namely there is a twisted section function $s$ (non-negative, measurable, compactly supported, with $\int s(tx)\,d\tau_A'=1$ whenever the twisted translate is in the support) and $J_A'(u,z)=\int \varphi_a(\mathrm{archIdentGL}(x^{-1}\delta_A(u,z)\sigma_{\mathrm{GL}}(x)))\,\mathrm{wt}(x)\,s(x)\,d\nu_A'$; and `hJA'0`: $J_A'(u,z)=0$ for $u\ne1$ when $\mathrm{glArch}\,\gamma(u,z)$ is not a norm. Complex numbers $J_F'(u,z,v)$ (`JF'`) with `hJF'`: for $u\ne1$, $v\in S_K$ and under the norm hypothesis at $v$, $J_F'(u,z,v)$ is the twisted weighted orbital integral at $\delta_F(u,z,v)$ with measure $\tau_F'(u,z,v)$, test function $\varphi_S(v)$, taken against the semi-local Haar measure and the semi-local weight $\sum_{w\mid v}\mathrm{weight}$ over the extensions $w$ of $v$ to $L$; and `hJF'0`: $J_F'(u,z,v)=0$ for $u\ne1$, $v\in S_K$ when the $v$-component is not a norm.
--
--   Conclusion. For $u\in K^\times$ with $u\ne1$ in $K$ (`hu1`), the function
--   $$z_S\;\longmapsto\;\xi(z_S)\Bigl(\bigl(J_A'(u,z_S)-\ell\,J_A(u,z_S)\bigr)\prod_{v\in S_K} I_F(u,z_S,v)\;+\;I_A(u,z_S)\sum_{v\in S_K}\bigl(J_F'(u,z_S,v)-\ell\,J_F(u,z_S,v)\bigr)\prod_{v'\in S_K\setminus\{v\}} I_F(u,z_S,v')\Bigr),$$
--   with $\ell=\mathrm{finrank}_K L$ regarded as a complex number, is integrable with respect to the measure $P_Z.\nu_S$.
--
--   This is the integrability statement for the discrepancy ("window") bracket attached to a single split conjugacy class $\mathrm{diag}(zu,z)$, $u\neq1$, in the cyclic base-change comparison of weighted hyperbolic terms: the bracket measures the failure of the $L$-side twisted weighted orbital integrals to equal $\ell$ times the $K$-side weighted ones, spread over the remaining unweighted factors. It supplies the integrability input for the centre-unfolding step in the packaging theorem [`AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_window_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_ne_one_unweighted`](thm.html#AutomorphicForm.sum_slotFamilyCoeff_mul_sum_mul_integral_window_eq_sum_prod_mul_windingDatum_coeff_of_forall_coeff_eq_of_ne_one_unweighted), whose hypotheses it repeats.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_mul_window_bracket_sPart_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one.lean

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

theorem AutomorphicForm.integrable_mul_window_bracket_sPart_of_isWeightedOrbitalIntegralOn_of_isTwistedWeightedOrbitalIntegralOn_of_ne_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
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

    (PZ : UnramifiedWhittaker.ProductMeasureData SK νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K SK)
    (hPν : ENNReal.ofReal PZ.c • PZ.νS = Measure.map (NumberField.Idele.partAt K SK)
      (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K ↑SK)))

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
    (u : Kˣ) (hu1 : (u : K) ≠ 1) :
    Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
        ((JA' u zS - (Module.finrank K L : ℂ) * JA u zS) * ∏ v ∈ SK, IF u zS v +
          IA u zS * ∑ v ∈ SK, (JF' u zS v - (Module.finrank K L : ℂ) * JF u zS v) * ∏ v' ∈ SK.erase v, IF u zS v')) PZ.νS := by sorry
