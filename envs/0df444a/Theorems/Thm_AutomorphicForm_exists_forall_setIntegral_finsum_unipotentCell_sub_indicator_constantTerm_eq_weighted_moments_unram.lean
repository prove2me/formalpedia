-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram
-- name    : AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/a115a177-dfe6-519c-be15-173c005aa2f6
-- title:
--   Truncated twisted unipotent term as weighted Hecke-word moments
-- statement:
--   Setting. Let $K \subseteq L$ be number fields with $L/K$ Galois, let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and let $\Phi_L$ be a subset of $\mathrm{GL}_2$ of the adele ring of $L$. On the group of ideles $(\mathbb{A}_L)^\times$ a Borel measurable structure and a Haar measure $\nu_{Z_L}$ are fixed, together with a set $\Omega_L$ which by `hΩL` is a fundamental domain for the image of $L^\times$ under the units map of $L \to \mathbb{A}_L$, relative to $\nu_{Z_L}$. Further data: $D$, an idelic Galois descent datum for $L/K$, that is a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is compatible with the inclusion of $L$ and continuous in each element; an element $\sigma$ of $\mathrm{Gal}(L/K)$ with `hgen` asserting that every $\tau$ lies in the subgroup of integer powers of $\sigma$; a finite set $S_L$ of primes of $\mathcal{O}_L$; and a homomorphism $\xi_L$ from the full subgroup of $(\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$.
--
--   Hypotheses on $S_L$ and $\xi_L$. `hSL`: every prime $w$ of $\mathcal{O}_L$ whose ramification index `ramificationIdx'` over the prime of $\mathcal{O}_K$ below it differs from $1$ belongs to $S_L$. `hξc`: the complex-valued function $z \mapsto \xi_L(z)$ is continuous on $(\mathbb{A}_L)^\times$. `hξt`: $\xi_L$ takes the value $1$ on the image of $L^\times$.
--
--   Test-function and Siegel data. A finite set $S$ of primes of $\mathcal{O}_K$, an archimedean test function $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, and for every prime $v$ of $\mathcal{O}_K$ a function $\varphi_S(v)$ on $\mathrm{GL}_2(L \otimes_K K_v)$. Reals $c,u,d_1,d_2$ with $0<c$, a compact set $T_c$ in $\mathrm{GL}_2(\mathbb{A}_L)$ and a set $\Phi_0$ subject to three conditions: `hΦ₀S`, that $\Phi_0$ is contained in the union over $y \in T_c$ of the right translates by $y$ of `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂`, the set of $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place has `localHeight` at least $c$ and `xWindowSq` at most $u^2$, and whose archimedean determinant norm at each infinite place lies in $[d_1,d_2]$; `hΦ₀s`, that on $\Phi_0$ the idele norm of $\det g$ lies in $[\alpha,\beta]$; and `hΦ₀`, that $\Phi_0$ is a fundamental domain for the image of $\mathrm{GL}_2(K)$-points, namely the range of `globalPoints (𝓞 L) L`, with respect to the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L` restricted to that determinant band.
--
--   Hecke-word data at a finite set $T$. The conclusion is universally quantified over a finite set $T$ of primes of $\mathcal{O}_K$ such that no prime $w$ of $\mathcal{O}_L$ lying over a $v \in T$ belongs to $S_L$ (so, by `hSL`, all such $w$ are unramified); over a choice $w_s(v)$, for each prime $v$ of $\mathcal{O}_K$, of a prime of $\mathcal{O}_L$ lying over $v$, and a map $w'$ from primes of $\mathcal{O}_K$ to primes of $\mathcal{O}_L$ with $(w'(v))$ equal to the $\sigma$-translate of $w_s(v)$ as ideals for $v \in T$; over elements $\varpi_v$ of the valuation ring of the completion at $w_s(v)$, irreducible for $v \in T$, with nonzero image $h_{\varpi}(v)$ in the completion for $v \in T$; over naturals $n_v$ and families $r_v : \mathrm{Fin}(n_v) \to \mathrm{GL}_2$ of the completion at $w_s(v)$ such that for $v \in T$ the family $r_v$ is a Hecke coset system (`IsHeckeCosetSystem`) for the subgroup [`LocalGL2.integralSubgroup`](def/LocalLanglands_LocalHeckeInstance.html#L13) — the image of $\mathrm{GL}_2$ of the valuation ring — and the element $\mathrm{diag}(\varpi_v,1)$, i.e. its members lie in the double coset, they cover it modulo the subgroup, and they are pairwise distinct modulo it; and over elements $z_v$ of $\mathrm{GL}_2$ of the completion at $w_s(v)$ whose matrix, for $v \in T$, is $\varpi_v$ times the identity.
--
--   Conclusion. For such data there exist complex numbers $\Lambda$ and $\kappa_0$ and complex-valued functions $c_1,c_2$ on the primes of $\mathcal{O}_K$ — independent of the word data below — with the following property. Let $k_v$ and $j_v$ ($v$ a prime of $\mathcal{O}_K$) be naturals, and let $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$ and $\varphi_f$ on $\mathrm{GL}_2$ of the finite adeles of $L$ satisfy `IsSemiLocalFactorization K L (S ∪ T) φ φa φf` for the semi-local family which at $v \in T$ is the function
--   $$x \mapsto \sum_{\iota : \mathrm{Fin}(k_v) \to \mathrm{Fin}(n_v)} \mathbf{1}_{\,\mathrm{semiLocalIntegralSet}\,K\,L\,v}\bigl( (\mathrm{semiLocalComponent}\,K\,L\,v\,\iota_{w_s(v)}( r_v(\iota(0)) \cdots r_v(\iota(k_v-1)) \, z_v^{\,j_v}))^{-1} x \bigr),$$
--   where $\iota_{w_s(v)}$ is [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of $\mathrm{GL}_2$ at $w_s(v)$ into $\mathrm{GL}_2$ of the finite adeles and the indicator has value $1$, and which at $v \notin T$ is $\varphi_S(v)$. Thus $\varphi_a$ is smooth with compact support in the archimedean matrix entries, $\varphi_f$ is locally constant with compact support, each member of the family at $v \in S \cup T$ is locally constant with compact support, $\varphi_f(h)$ equals the product over $v \in S \cup T$ of the family at the semi-local components of $h$ whenever all components outside $S \cup T$ are semi-locally integral and vanishes if some component outside $S \cup T$ is not, and $\varphi(g) = \varphi_a(\text{arch } g)\,\varphi_f(\text{fin } g)$.
--
--   Then there is $R_0 \in \mathbb{R}$ such that for every $R \ge R_0$ the following three assertions hold. Write, for $x \in \mathrm{GL}_2(\mathbb{A}_L)$ and $z \in (\mathbb{A}_L)^\times$,
--   $$\mathcal{K}(x,z) = \sum^{\mathrm f}_{\delta} \varphi\bigl(x^{-1}\,\delta\,{}^{\sigma_D}(z\,x)\bigr) - \mathbf{1}_{\{g \,:\, e^{R} < \mathrm{ht}(g)\}}(z\,x)\cdot \mathrm{CT}(z\,x),$$
--   where: the finsum runs over those $\delta \in \mathrm{GL}_2(L)$ for which some $\gamma$ in `unipotentCell K` — the set of elements of $\mathrm{GL}_2(K)$ whose matrix is not of type `IsCentralType` and has characteristic polynomial $(X-a)^2$ for some $a \in K$ — satisfies `normClassMap hgen` of the $\sigma$-twisted class of $\delta$ equal to the conjugacy class of $\gamma$; $\delta$ is viewed in $\mathrm{GL}_2(\mathbb{A}_L)$ through `globalPoints`, $z$ through the central scalar embedding, and ${}^{\sigma_D}$ denotes `sigmaAdelicAct K L D σ`; $\mathrm{ht}$ is the adelic height [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158), the product of the archimedean and finite heights; and
--   $$\mathrm{CT}(g) = \int_{t \in \mathbb{A}_L} \ \sum^{\mathrm f}_{\delta \in B} \varphi\bigl(x^{-1}\,\delta\,{}^{\sigma_D}(n(t)\,g)\bigr) \, d\nu(t),$$
--   with $n(t) = \begin{pmatrix}1&t\\0&1\end{pmatrix}$, with $B$ the set of $\gamma \in \mathrm{GL}_2(L)$ with lower-left entry $0$ and $\mathrm{N}_{L/K}(\gamma_{00}/\gamma_{11}) = 1$, and with measurable structure `adeleBorel` and measure $\nu$ those of the record `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`, so that $\nu$ is the additive adelic Haar measure conditioned on the adelic box.
--
--   (i) For every $x$, the function $z \mapsto \xi_L(z)\,\mathcal{K}(x,z)$ is integrable on $\Omega_L$ with respect to $\nu_{Z_L}$.
--
--   (ii) The function $x \mapsto \int_{\Omega_L} \xi_L(z)\,\mathcal{K}(x,z)\, d\nu_{Z_L}$ is integrable on $\Phi_0$ with respect to `adelicGLHaar (Fin 2) (𝓞 L) L`.
--
--   (iii) With $N_i =$ `HeckeEigensystem.cNorm` $(w'(i))$, the absolute norm of the ideal $w'(i)$, and $\xi_i = \xi_L(\det \,$`heckeGen (𝓞 L) L` $(w'(i)))$, put, for $i$ ranging over the elements of $T$,
--   $$A_i = \frac{1+(-1)^{k_i}}{2}\,\bigl(4 N_i \xi_i\bigr)^{\lfloor k_i/2\rfloor}\Bigl(\prod_{n < \lfloor k_i/2 \rfloor} \frac{2n+1}{2n+2}\Bigr)\,\xi_i^{\,j_i}, \qquad B_i = \bigl(1+(-1)^{k_i}\bigr)\bigl(4 N_i \xi_i\bigr)^{\lfloor k_i/2\rfloor}\,\xi_i^{\,j_i},$$
--   the exponents being natural-number halves and the rational product being cast from the reals. Then
--   $$\int_{\Phi_0} \int_{\Omega_L} \xi_L(z)\,\mathcal{K}(x,z)\, d\nu_{Z_L}\, d\,\mathrm{adelicGLHaar} = \Lambda\Bigl( R \prod_{i \in T} A_i + \sum_{p \in T} \bigl(c_1(p) B_p + c_2(p) A_p\bigr) \prod_{i \in T,\ i \ne p} A_i \Bigr) + \kappa_0 \prod_{i \in T} A_i.$$
--   The quantity $R$ occurring linearly is the real truncation parameter, cast to $\mathbb{C}$.
--
--   This is the unipotent-type contribution to the $\sigma$-twisted kernel on $\mathrm{GL}_2$ over $L$, folded against the idele class character $\xi_L$ and truncated at height $e^R$: its integral over a Siegel-type fundamental domain is an affine function of the truncation parameter $R$ whose coefficients are products, over the places of $T$, of local moment factors attached to each Hecke word of length $k_v$ and central shift $j_v$, with all constants independent of the word. It feeds the affine-in-$R$ reformulation [`AutomorphicForm.forall_exists_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_affine_unram`](thm.html#AutomorphicForm.forall_exists_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_affine_unram) and the slot-indexed form [`AutomorphicForm.exists_forall_mem_slotIndex_integrableOn_and_setIntegral_unipotentCell_eq_weighted_moments_self`](thm.html#AutomorphicForm.exists_forall_mem_slotIndex_integrableOn_and_setIntegral_unipotentCell_eq_weighted_moments_self), and rests on the local unramified computations of the twisted local factors and their Tate zeta integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram.lean

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

theorem
    AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [DecidableEq (HeightOneSpectrum (𝓞 K))] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hSL : ∀ w : HeightOneSpectrum (𝓞 L),
      (HeightOneSpectrum.under (𝓞 K) w).asIdeal.ramificationIdx' w.asIdeal ≠ 1 → w ∈ SL)
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
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))),
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
      ∃ Λ κ₀ : ℂ, ∃ c₁ c₂ : HeightOneSpectrum (𝓞 K) → ℂ,
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
            γ ∈ AutomorphicForm.unipotentCell K ∧
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
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x))) ΩL νZL) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
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
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
      (∫ x in Φ₀, (∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      ((∑ᶠ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
            γ ∈ AutomorphicForm.unipotentCell K ∧
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
              Algebra.norm K ((γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1) = 1},
            φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y)))
        (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ∂νZL)
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) =
        Λ * ((R : ℂ) *
            ∏ i : T,
              ((1 + (-1 : ℂ) ^ ks i) / 2 * (4 * (HeckeEigensystem.cNorm (w' i) *
                  ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                      Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (ks i / 2) *
                ((∏ n ∈ Finset.range (ks i / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js i) +
            ∑ p : T,
              (c₁ p *
                  ((1 + (-1 : ℂ) ^ ks p) * (4 * (HeckeEigensystem.cNorm (w' p) *
                      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' p)),
                          Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (ks p / 2) *
                    ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' p)),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js p) +
                  c₂ p *
                  ((1 + (-1 : ℂ) ^ ks p) / 2 * (4 * (HeckeEigensystem.cNorm (w' p) *
                      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' p)),
                          Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (ks p / 2) *
                    ((∏ n ∈ Finset.range (ks p / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                    ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' p)),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js p)) *
                ∏ i ∈ Finset.univ.erase p,
                  ((1 + (-1 : ℂ) ^ ks i) / 2 * (4 * (HeckeEigensystem.cNorm (w' i) *
                      ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                          Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (ks i / 2) *
                    ((∏ n ∈ Finset.range (ks i / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                    ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js i)) +
          κ₀ * ∏ i : T,
            ((1 + (-1 : ℂ) ^ ks i) / 2 * (4 * (HeckeEigensystem.cNorm (w' i) *
                ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ (ks i / 2) *
              ((∏ n ∈ Finset.range (ks i / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L (w' i)),
                  Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ js i) := by sorry
