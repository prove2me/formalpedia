-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable
-- name    : AutomorphicForm.integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/886b599d-b32d-53a9-a4d9-958d92d963ee
-- title:
--   Centre-integrated Euler factorisation of a hyperbolic class integral
-- statement:
--   Let $K$ be a number field, and equip the idele unit group $(\mathbb{A}_K)^\times = (\mathrm{AdeleRing}\ \mathcal{O}_K\ K)^\times$ with a Borel measurable structure and a Haar measure $\nu_{Z,K}$.
--
--   **Central character data.** $\xi$ is a monoid homomorphism from the full subgroup $\top$ of $(\mathbb{A}_K)^\times$ to $\mathbb{C}^\times$; `hξc` requires $z \mapsto \xi(z)$ to be continuous as a $\mathbb{C}$-valued function, `hξt` requires $\xi$ to be trivial on the image of $K^\times$ under the principal-idele embedding, and, for two finite sets $S, T$ of height-one primes of $\mathcal{O}_K$ with `hTS : Disjoint T S`, `hur` requires $\xi$ to be trivial on every idele unit of the form $\mathrm{Units.map}\ (\mathrm{finIncl})\ (\mathrm{localUnit}\ v\ t)$, i.e. $t$ placed in the $v$-component and $1$ elsewhere, for $v \notin S$ and $t \in (K_v)^\times$ of valuation $1$.
--
--   **Test function data.** $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$, $f_a$ on $\mathrm{GL}_2$ of the infinite adeles, $f_f$ on $\mathrm{GL}_2$ of the finite adeles and local functions $f_S(v)$ on $\mathrm{GL}_2(K_v)$ are complex valued, and `hf : IsUnitFactorization K (S ∪ T) f fa ff fS` asserts: $f_a$ is an archimedean test factor (given by a smooth function of the archimedean matrix entries and compactly supported); $f_f$ is locally constant with compact support; $f_S(v)$ is locally constant with compact support for every $v \in S \cup T$; $f_f(h) = \prod_{v \in S \cup T} f_S(v)(h_v)$ whenever all components $h_v$ with $v \notin S \cup T$ lie in the integral set $\mathrm{localIntegralSet}\ K\ v$ (the matrices in $\mathrm{GL}_2(K_v)$ which together with their inverses have entries in $\mathcal{O}_v$); $f_f(h) = 0$ if some component outside $S \cup T$ fails to lie in that set; and $f(g) = f_a(g_\infty) f_f(g_{\mathrm{fin}})$ for all $g$. The hypothesis `hcen` requires, for each $v \in T$, that $f_S(v)$ be invariant under left multiplication by any $c \in \mathrm{GL}_2(K_v)$ whose matrix is $\varepsilon \cdot 1$ with $|\varepsilon|_v = 1$.
--
--   **The class.** $\gamma \in \mathrm{GL}_2(K)$ and $u \in K^\times$ with $u \neq 1$ (`hu1`), and `hγ` requires $\gamma_{10} = 0$, $\gamma_{01} = 0$ and $\gamma_{00}/\gamma_{11} = u$. The adelic point of $\gamma$ is $\mathrm{globalPoints}\ \gamma$, the image of $\gamma$ under the entrywise principal-idele map; $\mathrm{centralScalar}\ z$ denotes the scalar matrix attached to an idele unit $z$, and $\mathrm{diagUnits2}\ x\ y$ the diagonal element $\mathrm{diag}(x,y)$.
--
--   **Centralizer measures and their normalisations.** A real constant $c_{\tau K} > 0$ is given together with a Haar measure $\tau_K$ on the centralizer of $\{\mathrm{globalPoints}\ \gamma\}$ in $\mathrm{GL}_2(\mathbb{A}_K)$ such that (`hτKc`) for every $g : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ the integral of $g$ over that centralizer against $\tau_K$ equals $c_{\tau K} \int g(\mathrm{diag}(p_1,p_2))\, d(\nu_{Z,K} \times \nu_{Z,K})(p)$. For each idele unit $z$, $\tau_G(z)$ is a Haar measure (`hτG`) on the centralizer of the single element $\mathrm{centralScalar}(z) \cdot \mathrm{diag}(u,1)$ (with $u$ taken as a principal idele unit), subject to the same identity with the same constant $c_{\tau K}$ (`hτGc`); $\tau_A(z)$ is a Haar measure (`hτA`) on the centralizer of the archimedean part of that element, and $\tau_F(z,v)$ a Haar measure (`hτF`) on the local centralizer at $v$ of its $v$-component, normalised by `hτF1` so that the preimage of $\mathrm{localIntegralSet}\ K\ v$ has measure $1$.
--
--   **Factorisation hypotheses.** A Haar measure $\nu_A$ on $\mathrm{GL}_2$ of the infinite adeles (`hνA`) and a real constant $c_G$ are given with `hG`: for every finite set of primes, every $f$, $f_a$, $f_S$ such that $f_a$ is almost everywhere strongly measurable for $\nu_A$, each $f_S(v)$ (over the given set) is almost everywhere strongly measurable for the local Haar measure $\mathrm{localHaar}\ K\ v$, $f(g)$ equals $f_a(g_\infty) \prod_v f_S(v)(g_v)$ whenever all components outside the set are integral, and $f(g) = 0$ when some such component is not integral, one has $\int f \, d(\mathrm{adelicGLHaar}) = c_G (\int f_a \, d\nu_A) \prod_v \int f_S(v) \, d(\mathrm{localHaar}\ K\ v)$. Similarly a constant $c_T > 0$ (`hcT`) is given with `hT`: the analogous factorisation of $\int W \, d\tau_G(z)$ as $c_T (\int W_a \, d\tau_A(z)) \prod_{v \in S'} \int W_S(v)\, d\tau_F(z,v)$, for functions $W$ on the centralizer of $\mathrm{centralScalar}(z)\cdot\mathrm{diag}(u,1)$ factorising over a finite set $S'$ in the same way, with the corresponding measurability hypotheses.
--
--   **Product measure data.** $P_Z$ is a $\mathrm{ProductMeasureData}$ for $S$ and $\nu_{Z,K}$ (a constant $P_Z.c > 0$, a measure $P_Z.\nu_S$, a projection $P_Z.\mathrm{projS}$, an order function $P_Z.\mathrm{ord}$, together with the clauses fixing the behaviour of $\mathrm{projS}$ off $S$, the decomposition of idele units integral off $S$ and a finite list of primes, the Tonelli identity for integrals over $\mathrm{unitIdelesOutside}$ and the measurability of those sets), subject to `hPo`: $P_Z.\mathrm{ord}$ is $\mathrm{Idele.ord}\ K$, `hPp`: $P_Z.\mathrm{projS}$ is $\mathrm{Idele.partAt}\ K\ S$, and `hPν`: $\mathrm{ofReal}(P_Z.c) \cdot P_Z.\nu_S$ is the pushforward under $\mathrm{Idele.partAt}\ K\ S$ of $\nu_{Z,K}$ restricted to the idele units integral outside $S$.
--
--   **Orbital integrals.** $I_K : (\mathbb{A}_K)^\times \to \mathbb{C}$ satisfies `hIK`: for every $z$, $I_K(z)$ is an orbital integral of $g \mapsto f(\mathrm{centralScalar}(z)\,g)$ at $\mathrm{globalPoints}\ \gamma$ for $\mathrm{adelicGLHaar}$ and $\tau_K$, i.e. there is a weight $w \geq 0$, measurable and compactly supported, with $\int_{Z(\gamma)} w(tx)\, d\tau_K = 1$ whenever the integrand at $x$ is non-zero, and $I_K(z) = \int f(\mathrm{centralScalar}(z)\, x^{-1}\gamma x) w(x)$. Likewise $I_A(z)$ is (`hIA`) an orbital integral of $f_a$ at the archimedean part of $\mathrm{centralScalar}(z)\cdot\mathrm{diag}(u,1)$ for $\nu_A$ and $\tau_A(z)$, and $I_F(z,v)$ is (`hIF`), for $v \in S$, a local orbital integral of $f_S(v)$ at the $v$-component of that element for $\mathrm{localHaar}\ K\ v$ and $\tau_F(z,v)$. The hypothesis `hWint` requires $z_S \mapsto \xi(z_S)\,(I_A(z_S) \prod_{v \in S} I_F(z_S,v))$ to be integrable for $P_Z.\nu_S$.
--
--   **Hecke shells at $T$.** Elements $\varpi_T(v) \in \mathcal{O}_v$ are given, irreducible for $v \in T$ (`hϖT`), and elements $t_T(v,e) \in \mathrm{GL}_2(K_v)$ with (`htT`) matrix $\mathrm{diag}(\varpi_T(v)^e u, \varpi_T(v)^e)$ for $v \in T$ and $e \in \mathbb{Z}$; $\tau_T(v,e)$ is a Haar measure on the local centralizer of $t_T(v,e)$ (`hτT`) giving measure $1$ to the preimage of $\mathrm{localIntegralSet}\ K\ v$ (`hτT1`), and $I_T(v,e)$ is (`hIT`), for $v \in T$, a local orbital integral of $f_S(v)$ at $t_T(v,e)$ for $\tau_T(v,e)$. Finally `hITsum` requires, for each $v \in T$, that $e \mapsto \|\xi(\det \mathrm{heckeGen}\ v)^e I_T(v,e)\|$ be summable over $\mathbb{Z}$, where $\mathrm{heckeGen}\ v$ is the adelic element with $v$-component $\mathrm{diag}(\varpi_v,1)$ and $1$ elsewhere.
--
--   **Conclusion.** Under these hypotheses,
--   $$\int_{(\mathbb{A}_K)^\times} \xi(z)\, I_K(z)\, d\nu_{Z,K}(z) = (c_G\, c_T^{-1}\, P_Z.c)\cdot A \cdot B \cdot C \cdot D,$$
--   where the real constant $c_G c_T^{-1} P_Z.c$ is coerced to $\mathbb{C}$ and:
--
--   $A$ is $1$ if $\mathrm{Idele.ord}\ K\ v$ of the principal idele unit attached to $u$ vanishes for every $v$ with $v \notin S$ and $v \notin T$, and $0$ otherwise;
--
--   $B$ is, in the case $u - 1 \neq 0$, the real number $\mathrm{TateGlobal.ideleNorm}\ K$ of $\mathrm{Idele.partAt}\ K\ S$ applied to the principal idele unit attached to $u - 1$ (that is, the distributive Haar character of $\mathbb{A}_K$ at that idele), coerced to $\mathbb{C}$, and $0$ otherwise (the alternative is vacuous, $u \neq 1$ being assumed);
--
--   $C = \prod_{v \in T} \|u_v - 1\|\, \sum_{e \in \mathbb{Z}}' \xi(\det \mathrm{heckeGen}\ v)^e\, I_T(v,e)$, where $u_v$ is the image of $u$ in $K_v$ and the norm is the $v$-adic one;
--
--   $D = \int \xi(z_S)\,\bigl(I_A(z_S) \prod_{v \in S} I_F(z_S,v)\bigr)\, dP_Z.\nu_S(z_S)$.
--
--   This is the per-class step in the adelic packaging of a $K$-side hyperbolic contribution: the central integral of an adelic orbital integral at the diagonal class with eigenvalue ratio $u$ is written as an Euler product, with the places in $S$ carried by a single integral over the $S$-part measure, the places in $T$ carried by absolutely convergent Hecke shell series, and the remaining places contributing an integrality condition on $u$ together with the global norm of $u - 1$ via the product formula. It is used in the assembly of the weighted sums of orbital integrals over hyperbolic classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
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

theorem AutomorphicForm.integral_mul_orbital_centralScalar_eq_mul_ideleNorm_mul_prod_tsum_mul_integral_of_isUnitFactorization_of_integrable
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (hTS : Disjoint T S)
    (hur : ∀ v ∉ S, ∀ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 →
      ξ ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ = 1)

    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (hf : AutomorphicForm.IsUnitFactorization K (S ∪ T) f fa ff fS)
    (hcen : ∀ v ∈ T, ∀ c : GL (Fin 2) (v.adicCompletion K),
      (∃ ε : v.adicCompletion K, Valued.v ε = 1 ∧
        (c : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = ε • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∀ y : GL (Fin 2) (v.adicCompletion K), fS v (c * y) = fS v y)

    (γ : GL (Fin 2) K) (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = (u : K))
    (cτK : ℝ) (hcτK : 0 < cτK)
    (τK : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    [τK.IsHaarMeasure]
    (hτKc : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂τK =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (IK : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIK : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (adelicGLHaar (Fin 2) (𝓞 K) K)
        (AutomorphicForm.globalPoints (𝓞 K) K γ) τK
        (fun g : GL (Fin 2) (AdeleRing (𝓞 K) K) => f (AutomorphicForm.centralScalar (𝓞 K) K z * g)) (IK z))

    (νA : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (hνA : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)) νA)
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
    (τG : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      Measure (Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K)))))
    (hτG : ∀ z, (τG z).IsHaarMeasure)
    (hτGc : ∀ z, ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      ∫ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          g (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) ∂(τG z) =
        cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK))
    (τA : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (Subgroup.centralizer
          ({AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
        (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
    (hτA : ∀ z, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τA z))
    (τF : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)),
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ z v, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF z v))
    (hτF1 : ∀ z v, τF z v (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (cT : ℝ) (hcT : 0 < cT)
    (hT : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (S' : Finset (HeightOneSpectrum (𝓞 K)))
        (W : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (Wa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
        (WS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
        AEStronglyMeasurable[AutomorphicForm.centralizerBorel (InfiniteAdeleRing K)
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))] (fun t => Wa t) (τA z) →
        (∀ v ∈ S', AEStronglyMeasurable[AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))]
            (fun t => WS v t) (τF z v)) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∀ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∈
              AutomorphicForm.localIntegralSet K v) →
            W t = Wa (AdelicLevel.glArch (𝓞 K) K t) *
              ∏ v ∈ S', WS v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t))) →
        (∀ t : Subgroup.centralizer ({(AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)} : Set (GL (Fin 2) (AdeleRing (𝓞 K) K))),
          (∃ v ∉ S', AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K t) ∉
              AutomorphicForm.localIntegralSet K v) → W t = 0) →
          ∫ t, W t ∂(τG z) = cT * (∫ t, Wa t ∂(τA z)) * ∏ v ∈ S', ∫ t, WS v t ∂(τF z v))

    (PZ : UnramifiedWhittaker.ProductMeasureData S νZK)
    (hPo : PZ.ord = NumberField.Idele.ord K) (hPp : PZ.projS = NumberField.Idele.partAt K S)
    (hPν : ENNReal.ofReal PZ.c • PZ.νS =
      Measure.map (NumberField.Idele.partAt K S)
        (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))

    (IA : (AdeleRing (𝓞 K) K)ˣ → ℂ)
    (hIA : ∀ z, AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) νA
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) (τA z) fa (IA z))
    (IF : (AdeleRing (𝓞 K) K)ˣ → HeightOneSpectrum (𝓞 K) → ℂ)
    (hIF : ∀ z, ∀ v ∈ S, AutomorphicForm.IsOrbitalIntegral K v
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z v) (fS v) (IF z v))

    (hWint : Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
      (IA zS * ∏ v ∈ S, IF zS v)) PZ.νS)
    (ϖT : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K) (hϖT : ∀ v ∈ T, Irreducible (ϖT v))
    (tT : ∀ v : HeightOneSpectrum (𝓞 K), ℤ → GL (Fin 2) (v.adicCompletion K))
    (htT : ∀ v ∈ T, ∀ e : ℤ, (tT v e : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(ϖT v : v.adicCompletion K) ^ e * algebraMap K (v.adicCompletion K) (u : K),
        (ϖT v : v.adicCompletion K) ^ e])
    (τT : ∀ (v : HeightOneSpectrum (𝓞 K)) (e : ℤ),
      @Measure (AutomorphicForm.localCentralizer K v (tT v e)) (AutomorphicForm.localCentralizerBorel K v (tT v e)))
    (hτT : ∀ v e, @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v (tT v e)) (τT v e))
    (hτT1 : ∀ v e, τT v e (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1)
    (IT : HeightOneSpectrum (𝓞 K) → ℤ → ℂ)
    (hIT : ∀ v ∈ T, ∀ e : ℤ, AutomorphicForm.IsOrbitalIntegral K v (tT v e) (τT v e) (fS v) (IT v e))

    (hITsum : ∀ v ∈ T, Summable fun e : ℤ =>
      ‖((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e * IT v e‖) :
    ∫ z : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * IK z ∂νZK =
      ((cG * cT⁻¹ * PZ.c : ℝ) : ℂ) *
        (if ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → v ∉ T → NumberField.Idele.ord K v (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) = 0
          then (1 : ℂ) else 0) *
        (if h1 : (u : K) - 1 ≠ 0 then
            ((NumberField.TateGlobal.ideleNorm K
                (NumberField.Idele.partAt K S (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Units.mk0 ((u : K) - 1) h1))) : ℝ) : ℂ)
          else 0) *
        (∏ v ∈ T, ((‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℝ) : ℂ) *
            ∑' e : ℤ, ((ξ ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ e *
              IT v e) *
        ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (IA zS * ∏ v ∈ S, IF zS v) ∂PZ.νS := by sorry
