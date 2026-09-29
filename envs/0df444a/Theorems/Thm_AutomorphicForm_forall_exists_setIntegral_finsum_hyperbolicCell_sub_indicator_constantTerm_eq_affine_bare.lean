-- Prove2me | Theorems.Thm_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare
-- name    : AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/3fcf692e-2967-5767-85cf-4325f212192f
-- title:
--   Affine dependence of the hyperbolic term on the truncation parameter
-- statement:
--   Throughout, $L/K$ is a Galois extension of number fields, $\sigma : L \simeq_K L$ is an automorphism such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integral powers of $\sigma$ (hypothesis `hgen`), and $D$ is an idèle Galois descent datum for $L/K$, i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is compatible with the action on $L$ and continuous in each component; [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) denotes the induced automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$, [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) the map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ and [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) the map sending an idèle $z$ to the scalar matrix $\mathrm{diag}(z,z)$.
--
--   The central data consist of: reals $\alpha, \beta$ with $0 < \alpha < \beta$; a set $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$; a Haar measure $\nu_{Z_L}$ on the idèle group $\mathbb{A}_L^\times$ (with the idèles carrying a measurable space that is the Borel structure of their topology) and a set $\Omega_L$ which, by the hypothesis `hΩL`, is a fundamental domain for the action on $\mathbb{A}_L^\times$ of the image of $L^\times$ under the map induced by $L \to \mathbb{A}_L$, with respect to $\nu_{Z_L}$; a finite set $S_L$ of finite places of $L$; and a homomorphism $\xi_L$ from the full subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$, subject to `hξc` (the associated $\mathbb{C}$-valued function on idèles is continuous) and `hξt` ($\xi_L$ takes the value $1$ on the image of $L^\times$).
--
--   The test-function data consist of a finite set $S$ of finite places of $K$, a function $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adèles of $L$, and for every finite place $v$ of $K$ a function $\varphi_{S,v}$ on $\mathrm{GL}_2(L \otimes_K K_v)$.
--
--   The geometric data consist of reals $c, u, d_1, d_2$ with $c > 0$, a compact set $T_c \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ and a set $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ subject to three hypotheses: `hΦ₀S`, that $\Phi_0$ is contained in the union over $y \in T_c$ of the right translates by $y$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` (those $g$ whose finite part lies in the integral subgroup $\mathrm{GL}_2(\widehat{\mathcal{O}}_L)$, whose local heights at all infinite places are $\ge c$, whose window quantities $\mathrm{xWindowSq}$ at all infinite places are $\le u^2$ and whose archimedean determinant norms lie in $[d_1,d_2]$); `hΦ₀s`, that $\Phi_0$ lies in the slab of those $g$ with $\|\det g\| \in [\alpha,\beta]$, the idèle norm being the module of the multiplication action on $\mathbb{A}_L$; and `hΦ₀`, that $\Phi_0$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(L)$ on $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` restricted to that slab.
--
--   The assertion is universally quantified over the following Hecke data. A finite set $T$ of finite places of $K$ with $2 \le |T|$, such that no place of $L$ above a place of $T$ belongs to $S_L$; a choice, for every finite place $v$ of $K$, of a place $w_v$ of $L$ above $v$ (an element of `v.Extension (𝓞 L)`), together with a function $v \mapsto w'_v$ into the finite places of $L$ satisfying $(w'_v)$'s prime ideal $= \sigma \cdot (w_v)$'s prime ideal for $v \in T$; elements $\varpi_v$ of the valuation ring of the completion $L_{w_v}$, irreducible for $v \in T$, with nonzero image in $L_{w_v}$ for $v \in T$ (hypothesis `hϖs0`); natural numbers $n_v$ and families $r_{v} : \mathrm{Fin}(n_v) \to \mathrm{GL}_2(L_{w_v})$ such that for $v \in T$ the family $r_v$ is a Hecke coset system ([`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15)) for the subgroup $U_v =$ image of $\mathrm{GL}_2(\mathcal{O}_{w_v})$ in $\mathrm{GL}_2(L_{w_v})$ and the element $\mathrm{diag}(\varpi_v,1)$: each $r_v(i)$ lies in the double coset $U_v \mathrm{diag}(\varpi_v,1) U_v$, every element of that double coset is left-$U_v$-equivalent to some $r_v(i)$, and $i \mapsto r_v(i) U_v$ is injective; finally elements $z_v \in \mathrm{GL}_2(L_{w_v})$ whose matrix is $\varpi_v$ times the identity for $v \in T$.
--
--   Under these hypotheses there exist two functions
--   $$\mu, \nu : (\text{finite places of } K \to \mathbb{N}) \to (\text{finite places of } K \to \mathbb{N}) \to \mathbb{C}$$
--   such that the following holds for all pairs of exponent functions $k, j$ on the finite places of $K$, and for every pair of functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adèles of $L$ which form a semi-local factorisation `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` with local factors given at $v \in T$ by
--   $$x \mapsto \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)} \mathbf{1}_{\mathcal{I}_v}\bigl( (\text{semi-local component at } v \text{ of } \textstyle\prod_{m} r_v(\iota(m)) \cdot z_v^{\,j_v}\text{, embedded at } w_v)^{-1} x \bigr),$$
--   where the product is taken in the order of $m$, the element is embedded into $\mathrm{GL}_2$ of the finite adèles by [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) at $w_v$ and then pushed to $\mathrm{GL}_2(L \otimes_K K_v)$ by `semiLocalComponent`, and $\mathcal{I}_v =$ `semiLocalIntegralSet K L v` is the set of matrices having, together with their inverses, all entries in the image of the semi-local integers; and given at $v \notin T$ by $\varphi_{S,v}$. (The factorisation condition comprises six clauses: $\varphi_a$ is an archimedean test factor, i.e. is given by a smooth function of the mixed-space entries and has compact support; $\varphi_f$ is locally constant with compact support; each local factor at a place of $S \cup T$ is locally constant with compact support; $\varphi_f(h)$ equals the product over $v \in S \cup T$ of the local factors evaluated at the semi-local components of $h$ whenever all components outside $S \cup T$ are integral; $\varphi_f(h) = 0$ as soon as some component outside $S \cup T$ fails to be integral; and $\varphi(g) = \varphi_a(g_\infty)\varphi_f(g_f)$.)
--
--   For such data there exists $R_0 \in \mathbb{R}$ such that for every real $R \ge R_0$ the three following statements hold. Write
--   $$A_\varphi(x,z) = \sum^{\mathrm{f}}_{\delta} \varphi\bigl(x^{-1}\, \delta\, \sigma_{\mathbb{A}}(\mathrm{diag}(z,z)\,x)\bigr),$$
--   the finsum being over those $\delta \in \mathrm{GL}_2(L)$ for which there is a $\gamma \in \mathrm{GL}_2(K)$ lying in [`AutomorphicForm.hyperbolicCell K`](def/AutomorphicForm_GL2ConjugacyCells.html#L32) (its characteristic polynomial is $(X-a)(X-b)$ with $a \ne b$) whose conjugacy class is the image of the $\sigma$-conjugacy class of $\delta$ under the norm map [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766); and write
--   $$B_{\varphi,R}(x,g) = \mathbf{1}_{\{H_L > e^{R}\}}(g)\cdot \int \Bigl( \sum^{\mathrm{f}}_{\delta}\varphi\bigl(x^{-1}\,\delta\,\sigma_{\mathbb{A}}(n(t)\,g)\bigr) \Bigr)\, d\tilde\nu(t),$$
--   where $H_L$ is the adelic height [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) (the product of the archimedean and finite heights of the two parts of $g$), $n(t) = \begin{pmatrix} 1 & t \\ 0 & 1\end{pmatrix}$ is [`AutomorphicForm.unipotentGL2`](def/AutomorphicForm_ConstantTerm.html#L17), the inner finsum runs over those $\gamma \in \mathrm{GL}_2(L)$ with $\gamma_{10} = 0$ and $N_{L/K}(\gamma_{00}/\gamma_{11}) \ne 1$, and $\tilde\nu$ is the measure component of `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`, namely the additive Haar measure of $\mathbb{A}_L$ conditioned on the adelic box `adelicBox L` (infinite part in the fundamental domain of the lattice basis, finite part integral), taken with the Borel structure `adeleBorel`; this is the truncated constant term [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) of the indicated function, evaluated at $g$. Put $F(x,z) = A_\varphi(x,z) - B_{\varphi,R}\bigl(x, \mathrm{diag}(z,z)\,x\bigr)$.
--
--   First, for every $x \in \mathrm{GL}_2(\mathbb{A}_L)$ the function $z \mapsto \xi_L(z)\,F(x,z)$ is integrable on $\Omega_L$ with respect to $\nu_{Z_L}$. Second, the function $x \mapsto \int_{\Omega_L} \xi_L(z) F(x,z)\, d\nu_{Z_L}(z)$ is integrable on $\Phi_0$ with respect to `adelicGLHaar (Fin 2) (𝓞 L) L`. Third, that double integral is exactly affine in the truncation parameter:
--   $$\int_{\Phi_0} \int_{\Omega_L} \xi_L(z)\, F(x,z)\, d\nu_{Z_L}(z)\, dx \; = \; R\cdot \nu(k)(j) + \mu(k)(j).$$
--   The coefficients $\mu$ and $\nu$ are chosen before $k$, $j$, $\varphi$, $\varphi_f$ and $R$, so they depend only on the data fixed above and on the exponents $k, j$, while the threshold $R_0$ may depend on $k$, $j$, $\varphi$ and $\varphi_f$. No bound on $|\mu(k)(j)| + |\nu(k)(j)|$ in terms of $k$ and $j$ is asserted.
--
--   This is the hyperbolic-type contribution to the geometric side of the twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$, evaluated against a test function whose components at the places of $T$ are Hecke words of length $k_v$ in the coset representatives of the double coset of $\mathrm{diag}(\varpi_v,1)$ twisted by central powers $z_v^{j_v}$: after truncation at height $e^{R}$ and integration over the idèle-class direction and over a fundamental domain in the determinant slab, the resulting quantity is an affine function of $R$ with coefficients independent of $R$. The statement is the bare identity, without any accompanying estimate on the affine coefficients; it feeds the versions of the hyperbolic-term identity carrying a coefficient bound, the passage to the limit as the truncation parameter grows, and the comparison of Hecke coefficients under matching.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_affine_bare
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ • (ws v).1.asIdeal) →
      ∀ (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
        (∀ v ∈ T, Irreducible (ϖs v)) →
      ∀ (hϖs0 : ∀ v ∈ T,
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) ≠ 0)
        (ns : HeightOneSpectrum (𝓞 K) → ℕ)
        (rTs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (ns v) → GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
            (LocalGL2.diagPi (ϖs v) (hϖs0 v hv)) (rTs v)) →
      ∀ (zs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) ((ws v).1.adicCompletion L)),
        (∀ v ∈ T, (zs v : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
          algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) (ϖs v) •
            (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L))) →
      ∃ μ ν : (HeightOneSpectrum (𝓞 K) → ℕ) → (HeightOneSpectrum (𝓞 K) → ℕ) → ℂ,
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φ : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (S ∪ T) φ φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 L) L, IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ =>
        ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.hyperbolicCell K ∧
            LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ *
              AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x))) -
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R))
        (@AutomorphicForm.constantTerm _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
          (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
            (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
          (fun t => AutomorphicForm.unipotentGL2 t)
          (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L |
            (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
      (R : ℂ) * ν ks js + μ ks js := by sorry
