-- Prove2me | Theorems.Thm_AutomorphicForm_exists_weightedClassIntegral_eq_mul_archWindow_mul_prod_add_mul_sum_window_and_isWeightedOrbitalIntegral_of_isUnitFactorization_of_coupled
-- name    : AutomorphicForm.exists_weightedClassIntegral_eq_mul_archWindow_mul_prod_add_mul_sum_window_and_isWeightedOrbitalIntegral_of_isUnitFactorization_of_coupled
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/047b89e5-a277-57f8-860d-84e9ca8bfe97
-- title:
--   Euler expansion of a weighted adelic orbital integral at a diagonal class
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ its adele ring, $\mathbb{A}_{K,\infty}$ its ring of infinite adeles and, for a finite place $v$, $K_v$ the $v$-adic completion; `localIntegralSet K v` is the set of $g \in \mathrm{GL}_2(K_v)$ such that both $g$ and $g^{-1}$ have entries in the ring of $v$-adic integers, `localHaar K v` is the Haar measure on $\mathrm{GL}_2(K_v)$ normalised to give that set mass $1$, `adelicGLHaar` and `archHaarK` are Haar measures on $\mathrm{GL}_2(\mathbb{A}_K)$ and $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$, `centralScalar` sends an idele $z$ to the scalar matrix $z\cdot 1$, `diagUnits2 x y` is the invertible diagonal matrix $\mathrm{diag}(x,y)$, `globalPoints` is the map $\mathrm{GL}_2(K) \to \mathrm{GL}_2(\mathbb{A}_K)$ induced by $K \to \mathbb{A}_K$, and `adelicWeyl` is the image in $\mathrm{GL}_2(\mathbb{A}_K)$ of the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
--
--   Data and hypotheses. A Haar measure $\nu_{Z,K}$ on the idele group $\mathbb{A}_K^\times$ is fixed, together with two disjoint finite sets $S_K$ and $T$ of finite places of $K$ (the hypothesis `hTS` states that $T$ and $S_K$ are disjoint).
--
--   Test data: a function $f_{a,K}$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ which is an archimedean test factor, that is, $f_{a,K}(g)$ is a $C^\infty$ function of the matrix entries of $g$ read in the mixed space of $K$, and $f_{a,K}$ has compact support; a family $f_{S_K}$ of functions on the groups $\mathrm{GL}_2(K_v)$ whose members at $v \in S_K$ are local test functions (locally constant with compact support); a second family $f_T$ whose members at $v \in T$ are local test functions; and functions $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ and $f_f$ on $\mathrm{GL}_2$ of the finite adeles such that `hf` holds: $f_{a,K}$ is an archimedean test factor, $f_f$ is locally constant with compact support, the local factor chosen at each $v \in S_K \cup T$ (namely $f_T(v)$ if $v \in T$ and $f_{S_K}(v)$ otherwise) is a local test function, $f_f(h) = \prod_{v \in S_K \cup T} (\text{local factor at } v)(h_v)$ for every $h$ all of whose components outside $S_K \cup T$ lie in `localIntegralSet`, $f_f(h) = 0$ as soon as some component of $h$ outside $S_K \cup T$ lies outside `localIntegralSet`, and $f(g) = f_{a,K}(g_\infty) f_f(g_{\mathrm{fin}})$ for all $g$.
--
--   Global normalisation: a measure $\nu_A$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ (with the Borel structure `glBorelOf`), required by `hνA` to be `archHaarK K`, a real constant $c_G$, and the hypothesis `hG`, which asserts for every finite set $S$ of finite places and every triple of functions $(f, f_a, f_S)$ — with $f_a$ almost everywhere strongly measurable for $\nu_A$, each $f_S(v)$, $v \in S$, almost everywhere strongly measurable for `localHaar K v`, $f(g) = f_a(g_\infty)\prod_{v \in S} f_S(v)(g_v)$ whenever all components of $g$ outside $S$ lie in `localIntegralSet`, and $f(g) = 0$ whenever some component outside $S$ does not — the product formula
--   $$\int f \, d(\mathrm{adelicGLHaar}) = c_G \Big(\int f_a \, d\nu_A\Big) \prod_{v \in S} \int f_S(v) \, d(\mathrm{localHaar}\,K\,v).$$
--
--   Torus measures. For $u \in K^\times$ and an idele $z$ write $\gamma(u,z) = \mathrm{centralScalar}(z)\cdot \mathrm{diag}(u,1)$, where $u$ is transported to $\mathbb{A}_K^\times$ by the structure map. The data comprise: a measure $\tau_G(u,z)$ on the centraliser of $\gamma(u,z)$ in $\mathrm{GL}_2(\mathbb{A}_K)$, Haar whenever $u \neq 1$ in $K$ (`hτG`), and satisfying the normalisation `hτGc`: for $u \neq 1$ and every function $g$ on $\mathrm{GL}_2(\mathbb{A}_K)$, the integral of $g$ over that centraliser against $\tau_G(u,z)$ equals $c_{\tau,K}$ times the integral of $(p_1,p_2) \mapsto g(\mathrm{diag}(p_1,p_2))$ over $\mathbb{A}_K^\times \times \mathbb{A}_K^\times$ against $\nu_{Z,K} \times \nu_{Z,K}$, where $c_{\tau,K} > 0$; a measure $\tau_A(u,z)$ on the centraliser of the archimedean component of $\gamma(u,z)$, Haar for $u \neq 1$ (`hτA`); and measures $\tau_F(u,z,v)$ on the local centralisers of the $v$-components of $\gamma(u,z)$, Haar for $u \neq 1$ (`hτF`) and assigning mass $1$ to the preimage of `localIntegralSet K v` (`hτF1`). Finally a constant $c_T > 0$ and the hypothesis `hT`, the centraliser analogue of `hG`: for $u \neq 1$, any $z$, any finite set $S$ and any triple $(W, W_a, W_S)$ with $W_a$ almost everywhere strongly measurable for $\tau_A(u,z)$, each $W_S(v)$, $v \in S$, almost everywhere strongly measurable for $\tau_F(u,z,v)$, $W(t) = W_a(t_\infty)\prod_{v \in S} W_S(v)(t_v)$ for $t$ in the adelic centraliser all of whose components outside $S$ lie in `localIntegralSet`, and $W(t) = 0$ when some such component does not, one has $\int W \, d\tau_G(u,z) = c_T (\int W_a \, d\tau_A(u,z)) \prod_{v \in S} \int W_S(v) \, d\tau_F(u,z,v)$.
--
--   Window values. Four families of unweighted values: $I_A(u,z)$ is, for $u \neq 1$, an orbital integral of $f_{a,K}$ at the archimedean component of $\gamma(u,z)$ with respect to $\nu_A$ and $\tau_A(u,z)$, meaning that there is a non-negative measurable compactly supported $w$ with $\int_{\text{centraliser}} w(tx)\,d\tau_A(u,z) = 1$ whenever $f_{a,K}(x^{-1}\gamma_\infty x) \neq 0$, such that $I_A(u,z) = \int f_{a,K}(x^{-1}\gamma_\infty x) w(x)\, d\nu_A$; $I_F(u,z,v)$, for $u \neq 1$ and $v \in S_K$, is the corresponding local orbital integral of $f_{S_K}(v)$ at the $v$-component of $\gamma(u,z)$ against $\tau_F(u,z,v)$ and `localHaar K v`; $I_T(u,z,v)$ is the same for $f_T(v)$ at $v \in T$; and $I_U(u,z,v)$ is the same for the indicator function of `localIntegralSet K v` (with value $1$) at $v \notin S_K \cup T$. Two families of weighted values: $J_A(u,z)$, for $u \neq 1$, is a weighted orbital integral of $f_{a,K}$ at the archimedean component of $\gamma(u,z)$ with the archimedean weight $y \mapsto -\log \mathrm{archHeight}(y) - \log \mathrm{archHeight}(w_\infty y)$, $w_\infty$ the archimedean component of `adelicWeyl`, that is, $J_A(u,z) = \int f_{a,K}(x^{-1}\gamma_\infty x)\,\mathrm{wt}(x)\,s(x)\, d\nu_A$ for some section function $s$ as above; and $J_F(u,z,v)$, for $u \neq 1$ and $v \in S_K$, is the local weighted orbital integral of $f_{S_K}(v)$ with the local weight `LocalWeight.weight` at the $v$-component of $\gamma(u,z)$ against $\tau_F(u,z,v)$.
--
--   The class. An element $\gamma \in \mathrm{GL}_2(K)$ with $\gamma_{10} = \gamma_{01} = 0$ and $\gamma_{00}/\gamma_{11} \neq 1$, together with units $u_\gamma, d_\gamma \in K^\times$ with $u_\gamma = \gamma_{00}/\gamma_{11}$ and $d_\gamma = \gamma_{11}$; a Haar measure $\tau_K$ on the centraliser of `globalPoints γ` in $\mathrm{GL}_2(\mathbb{A}_K)$ satisfying the same normalisation `hτKc` as the $\tau_G(u,z)$, namely that integration against $\tau_K$ equals $c_{\tau,K}$ times the double integral over diagonal ideles against $\nu_{Z,K} \times \nu_{Z,K}$; an idele $z$; and a complex number $J$ which, by `hJ`, is a weighted orbital integral of $g \mapsto f(\mathrm{centralScalar}(z)\,g)$ on $\mathrm{GL}_2(\mathbb{A}_K)$ against `adelicGLHaar`, at the element `globalPoints γ`, with respect to $\tau_K$, for the adelic weight $x \mapsto -\log \mathrm{adelicHeight}(x) - \log \mathrm{adelicHeight}(\mathrm{adelicWeyl}\cdot x)$: that is, $J = \int f(\mathrm{centralScalar}(z)\, x^{-1}\gamma_{\mathbb{A}} x)\,\mathrm{wt}(x)\, s(x)\, d(\mathrm{adelicGLHaar})$ for some section function $s$ for this integrand at $\gamma_{\mathbb{A}} = \mathrm{globalPoints}(\gamma)$ and $\tau_K$.
--
--   Conclusion. Write $z' = z \cdot d_\gamma$ for the idele obtained from $z$ by multiplying by the image of $d_\gamma$; the relevant class is $\gamma(u_\gamma, z') = \mathrm{centralScalar}(z')\cdot\mathrm{diag}(u_\gamma,1)$, which is $\mathrm{centralScalar}(z)\cdot\mathrm{globalPoints}(\gamma)$. Then there exist a finite set $T_1$ of finite places with $S_K \cup T \subseteq T_1$ and a family of complex numbers $J X_v$, indexed by the finite places, such that:
--
--   (i) $I_U(u_\gamma, z', v) = 1$ for every $v \notin T_1$;
--
--   (ii) for every $v \notin S_K$, the number $J X_v$ is a local weighted orbital integral, with the weight `LocalWeight.weight`, at the $v$-component of $\gamma(u_\gamma,z')$, with respect to $\tau_F(u_\gamma, z', v)$, of the function $f_T(v)$ if $v \in T$ and of the indicator function of `localIntegralSet K v` with value $1$ otherwise;
--
--   (iii) for every finite set $T_0$ of finite places with $T_1 \subseteq T_0$,
--   $$J = c_G\, c_T^{-1}\Big( J_A(u_\gamma,z') \prod_{v \in T_0} I_v \; + \; I_A(u_\gamma,z') \sum_{v \in T_0} J_v \prod_{u \in T_0 \setminus \{v\}} I_u \Big),$$
--   where $I_v$ denotes $I_F(u_\gamma,z',v)$ for $v \in S_K$, $I_T(u_\gamma,z',v)$ for $v \in T$ and $I_U(u_\gamma,z',v)$ otherwise, and $J_v$ denotes $J_F(u_\gamma,z',v)$ for $v \in S_K$ and $J X_v$ otherwise.
--
--   This is the Euler expansion of the height-weighted global orbital integral attached to a regular split (diagonal) rational class: the weighted adelic integral is expressed as a sum of products of one weighted local or archimedean factor with unweighted factors at all remaining places, uniformly in the auxiliary finite set $T_0$ over which the product is truncated. It is the form in which the contribution of a hyperbolic class enters the comparison of weighted trace formulae, and it is invoked by the statements that evaluate weighted class contributions in the level comparison and by the transfer of those contributions to the twisted side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_weightedClassIntegral_eq_mul_archWindow_mul_prod_add_mul_sum_window_and_isWeightedOrbitalIntegral_of_isUnitFactorization_of_coupled.lean

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

open AutomorphicForm in

theorem AutomorphicForm.exists_weightedClassIntegral_eq_mul_archWindow_mul_prod_add_mul_sum_window_and_isWeightedOrbitalIntegral_of_isUnitFactorization_of_coupled
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T SK)

    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfaK : AutomorphicForm.IsArchTestFactor K faK)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfSK : ∀ v ∈ SK, AutomorphicForm.IsLocalTestFn K v (fSK v))
    (fT : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hfT : ∀ v ∈ T, AutomorphicForm.IsLocalTestFn K v (fT v))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K (SK ∪ T) f faK ff (fun v => if v ∈ T then fT v else fSK v))

    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (cG : ℝ)
    (hG : ∀ (S : Finset (HeightOneSpectrum (𝓞 K)))
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
            cG * (∫ x, fa x ∂νA) * ∏ v ∈ S, ∫ y, fS v y ∂(AutomorphicForm.localHaar K v))

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
    (hνA : νA = AutomorphicForm.archHaarK K)

    (IA : Kˣ → (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ u z, ((u : Kˣ) : K) ≠ 1 → AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA u z) faK (IA u z))
    (IF : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ SK, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fSK v) (IF u z v))
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

    (IT : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIT : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∈ T, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v) (fT v) (IT u z v))
    (IU : Kˣ → (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIU : ∀ u z, ((u : Kˣ) : K) ≠ 1 → ∀ v ∉ SK ∪ T, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF u z v)
        ((AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (IU u z v))

    (γ : GL (Fin 2) K)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1)
    (uγ dγ : Kˣ)
    (huγ : (uγ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1)
    (hdγ : (dγ : K) = (γ : Matrix (Fin 2) (Fin 2) K) 1 1)

    (τK : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτK : τK.IsHaarMeasure)
    (hτKc : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (s : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂τK =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (z : (AdeleRing (𝓞 K) K)ˣ)

    (J : ℂ)
    (hJ : AutomorphicForm.IsWeightedOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
      (fun x : GL (Fin 2) (AdeleRing (𝓞 K) K) =>
        -Real.log (NumberField.AdelicHeight.adelicHeight K x)
          - Real.log (NumberField.AdelicHeight.adelicHeight K (AutomorphicForm.adelicWeyl (𝓞 K) K * x)))
      (AutomorphicForm.globalPoints (𝓞 K) K γ) τK
      (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) J) :
    ∃ T₁ : Finset (HeightOneSpectrum (𝓞 K)), SK ∪ T ⊆ T₁ ∧
    ∃ JX : HeightOneSpectrum (𝓞 K) → ℂ,
      (∀ v ∉ T₁, IU uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) v = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → AutomorphicForm.IsWeightedOrbitalIntegral K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) uγ) 1))) (τF uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) v)
        (if v ∈ T then fT v else (AutomorphicForm.localIntegralSet K v).indicator fun _ => (1 : ℂ)) (JX v)) ∧
      ∀ T₀ : Finset (HeightOneSpectrum (𝓞 K)), T₁ ⊆ T₀ →
        J = cG * cT⁻¹ *
          (JA uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) * ∏ v ∈ T₀, (if v ∈ SK then IF uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) v else if v ∈ T then IT uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) v else IU uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) v) +
            IA uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) *
              ∑ v ∈ T₀, (if v ∈ SK then JF uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) v else JX v) *
                ∏ u ∈ T₀.erase v, (if u ∈ SK then IF uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) u else if u ∈ T then IT uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) u else IU uγ (z * (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) dγ)) u)) := by sorry
