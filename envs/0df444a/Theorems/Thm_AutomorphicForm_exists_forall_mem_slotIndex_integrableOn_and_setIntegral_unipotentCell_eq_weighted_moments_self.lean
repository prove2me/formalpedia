-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_mem_slotIndex_integrableOn_and_setIntegral_unipotentCell_eq_weighted_moments_self
-- name    : AutomorphicForm.exists_forall_mem_slotIndex_integrableOn_and_setIntegral_unipotentCell_eq_weighted_moments_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/19b2902a-c842-52df-9690-958c689630ee
-- title:
--   Truncated unipotent contributions along a slot family over K
-- statement:
--   Setting. Let $K$ and $L$ be number fields with $L/K$ a finite Galois extension, and let $\alpha,\beta\in\mathbb R$ satisfy $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`). Further data: a finite set $S_K$ of finite places of $K$; an archimedean factor $f_{a,K}\colon \mathrm{GL}_2(K\otimes\mathbb R)\to\mathbb C$ on the infinite adeles; for each finite place $v$ of $K$ a function $f_{S_K,v}\colon \mathrm{GL}_2(K_v)\to\mathbb C$; a set $\Phi_K\subseteq \mathrm{GL}_2(\mathbb A_K)$; a Haar measure $\nu_{Z_K}$ on the idele group $\mathbb A_K^\times$ together with a set $\Omega_K\subseteq\mathbb A_K^\times$; a monoid homomorphism $\xi_K$ from the full subgroup $\top$ of $\mathbb A_K^\times$ to $\mathbb C^\times$; an ideal $N'$ of $\mathcal O_K$; and an archimedean type family $\mathrm{tys}_K$ for $K$, that is, a cardinality function on the infinite places of $K$ together with, for each infinite place $w$ and each index below that cardinality, a representation datum at $w$.
--
--   Hypotheses on these data. The slab condition `hΦKs` requires $\Phi_K\subseteq\{g: \mathrm{ideleNorm}_K(\det g)\in[\alpha,\beta]\}$, where the idele norm is the modulus of the distinguished Haar character of $\mathbb A_K$; the hypothesis `hΦK` requires $\Phi_K$ to be a fundamental domain for the action of the image of $\mathrm{GL}_2(K)$ in $\mathrm{GL}_2(\mathbb A_K)$ with respect to the adelic Haar measure $\mathrm{adelicGLHaar}$ restricted to that slab. The hypothesis `hΩK` requires $\Omega_K$ to be a fundamental domain for the image of $K^\times$ in $\mathbb A_K^\times$ with respect to $\nu_{Z_K}$. The character hypotheses are `hξKc`, continuity of $z\mapsto \xi_K(z)$ as a $\mathbb C$-valued function, and `hξKt`, triviality of $\xi_K$ on the image of $K^\times$; thus $\xi_K$ is a continuous idele class character. The level hypothesis `hN'` requires every finite place $v$ whose prime ideal divides $N'$ to lie in $S_K$.
--
--   Quantified local data. The assertion is made for every finite set $T$ of finite places of $K$ disjoint from $S_K$; every choice $w_\bullet$ assigning to each finite place $v$ of $K$ an extension of $v$ to $\mathcal O_L$ (a place of $L$ lying under which $v$ lies); every family $\varpi_\bullet$ with $\varpi_v$ in the valuation ring of $K_v$, such that $\varpi_v$ is irreducible for $v\in T$ and (`hϖKs0`) the image of $\varpi_v$ in $K_v$ is nonzero for $v\in T$; every function $n_\bullet$ to $\mathbb N$ and every family $r_\bullet$ with $r_v\colon \mathrm{Fin}(n_v)\to \mathrm{GL}_2(K_v)$ such that for each $v\in T$ the tuple $r_v$ is a Hecke coset system for the subgroup $\mathrm{LocalGL2.integralSubgroup}$, the image of $\mathrm{GL}_2(\mathcal O_v)$ in $\mathrm{GL}_2(K_v)$, and the element $\mathrm{LocalGL2.diagPi}(\varpi_v)=\mathrm{diag}(\varpi_v,1)$: each $r_v(i)$ lies in the double coset $U\varpi U$, every element of that double coset agrees with some $r_v(i)$ modulo $U$ on the right, and $i\mapsto r_v(i)U$ is injective; and every family $z_\bullet$ with $z_v\in \mathrm{GL}_2(K_v)$ such that for $v\in T$ the matrix of $z_v$ is the scalar matrix $\varpi_v\cdot 1$.
--
--   Conclusion, first layer. There exist $\Lambda,\kappa_0\in\mathbb C$ and functions $c_1,c_2$ from the finite places of $K$ to $\mathbb C$, independent of everything quantified below, with the following property. Let $k_\bullet,j_\bullet$ be functions from the finite places of $K$ to $\mathbb N$, and let $\mathrm{fam}$ assign to each dependent function $m$ (sending each $v\in T$ to an exponent vector in $\mathrm{Fin}\,2\to_{\mathrm f}\mathbb N$) a function $\mathrm{fam}\,m\colon \mathrm{GL}_2(\mathbb A_K)\to\mathbb C$. The admissibility hypothesis is imposed for every $m$ in $\mathrm{SatakeCombination.slotIndex}\,K\,L\,w_\bullet\,k_\bullet\,j_\bullet\,T$, the $T$-indexed dependent product of the supports of the polynomials $\mathrm{slotWord}\,K\,L\,w_\bullet\,v\,(k_v)\,(j_v)=\mathrm{univWord}(\mathrm{slotDeg}\,K\,L\,w_\bullet\,v-1)\,(k_v)\,(j_v)$ in two variables, and reads: $\mathrm{fam}\,m$ is invariant under left and right translation by the subgroup $\mathrm{principalLevel}(\mathcal O_K,K,N')\sqcap\mathrm{finiteAdelicGL2Subgroup}\,K$ (the principal level subgroup of level $N'$ intersected with the kernel of the archimedean projection $\mathrm{glArch}$); $\mathrm{fam}\,m$ is archimedean bi-finite of type $\mathrm{tys}_K$, meaning $g\mapsto \mathrm{fam}\,m\,(g^{-1})$ lies in the archimedean cut submodule and $\mathrm{fam}\,m$ lies in the archimedean dual cut submodule of that type family; $f_{a,K}$ is an archimedean test factor, that is, it is a smooth function of the archimedean matrix entries and has compact support; each $f_{S_K,v}$ with $v\in S_K$ is locally constant with compact support; and there exists $f_f\colon \mathrm{GL}_2(\mathbb A_{K,\mathrm f})\to\mathbb C$, locally constant with compact support, such that (i) for every $h$ all of whose components at places outside $S_K\cup T$ lie in $\mathrm{localIntegralSet}$ (the set of $g$ with both $g$ and $g^{-1}$ having entries in $\mathcal O_v$), $f_f(h)$ equals the product over $v\in S_K\cup T$ of the $v$-component of $h$ evaluated under the function which at $v\in T$ is
--   $$x\mapsto \sum_{\iota\colon \mathrm{Fin}(m_v(0))\to \mathrm{Fin}(n_v)} \mathbf 1_{\mathrm{localIntegralSet}}\Big(\big(r_v(\iota(0))\cdots r_v(\iota(m_v(0)-1))\cdot z_v^{\,m_v(1)}\big)^{-1}x\Big)$$
--   and at $v\notin T$ is $f_{S_K,v}$; (ii) $f_f(h)=0$ whenever some component of $h$ at a place outside $S_K\cup T$ fails to lie in $\mathrm{localIntegralSet}$; and (iii) $\mathrm{fam}\,m\,(g)=f_{a,K}(\mathrm{glArch}\,g)\cdot f_f(\mathrm{glFin}\,g)$ for all $g$.
--
--   Conclusion, second layer. Under this admissibility hypothesis there exists $R_0\in\mathbb R$ such that for every $R\ge R_0$ and every $m$ in the above slot index set the following three assertions hold. Write $F_{m,x,R}(z)$ for the integrand
--   $$\xi_K(z)\Big(K^{\mathrm{unip}}_{\mathrm{fam}\,m}(x,\,z\cdot x)\;-\;\mathbf 1_{\{g\,:\,e^R<\mathrm{adelicHeight}_K(g)\}}\!\left(C_{m,x}\right)(z\cdot x)\Big),$$
--   where $z\cdot x$ denotes $\mathrm{centralScalar}(z)\,x$; where $K^{\mathrm{unip}}_{f}(x,y)=\sum^{\mathrm f}_{\gamma\in\mathrm{unipotentCell}\,K} f(x^{-1}\,\gamma\,y)$ is the finsum over the elements of $\mathrm{GL}_2(K)$ of unipotent type, embedded by $\mathrm{globalPoints}$; and where $C_{m,x}$ is the constant term function $g\mapsto \int \Phi_{m,x}\big(\mathrm{unipotentGL2}(t)\,g\big)\,d\nu(t)$, the integration being over the adele ring with the adele Borel structure and the measure $\nu$ of $\mathrm{productionPinsOf}\,K\,\Phi_K\,(M\mapsto \mathrm{principalLevel}(\mathcal O_K,K,M)\sqcap\mathrm{finiteAdelicGL2Subgroup}\,K)\,(v\mapsto \mathrm{heckeGen}\,v)\,(\mathrm{adelicBox}\,K)$, namely the adelic additive Haar measure conditioned on the adelic box, $\mathrm{unipotentGL2}(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$, and
--   $$\Phi_{m,x}(y)=\sum^{\mathrm f}_{\gamma}\ \mathrm{fam}\,m\,(x^{-1}\,\gamma\,y),\qquad \gamma\in\{\gamma\in\mathrm{GL}_2(K): \gamma_{10}=0,\ \gamma_{00}/\gamma_{11}=1\}.$$
--
--   (a) For every $x\in \mathrm{GL}_2(\mathbb A_K)$ the function $z\mapsto F_{m,x,R}(z)$ is integrable on $\Omega_K$ with respect to $\nu_{Z_K}$.
--
--   (b) The function $x\mapsto \int_{\Omega_K}F_{m,x,R}(z)\,d\nu_{Z_K}(z)$ is integrable on $\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta$ (the domain component of the canonically chosen truncation datum for $(\alpha,\beta)$) with respect to the adelic Haar measure on $\mathrm{GL}_2(\mathbb A_K)$.
--
--   (c) With the abbreviations, for $i$ ranging over the places in $T$, $a_i=m_i(0)$, $b_i=m_i(1)$, $\chi_i=\xi_K\big(\det \mathrm{heckeGen}(\mathcal O_K,K,i)\big)$, $c_{\mathrm N}(i)=\mathrm{cNorm}(i)=\#(\mathcal O_K/i)$ viewed in $\mathbb C$, and
--   $$A_i=\frac{1+(-1)^{a_i}}{2}\,\big(4\,c_{\mathrm N}(i)\chi_i\big)^{\lfloor a_i/2\rfloor}\Big(\prod_{n<\lfloor a_i/2\rfloor}\frac{2n+1}{2n+2}\Big)\chi_i^{\,b_i},\qquad B_i=\big(1+(-1)^{a_i}\big)\big(4\,c_{\mathrm N}(i)\chi_i\big)^{\lfloor a_i/2\rfloor}\chi_i^{\,b_i},$$
--   the inner product of fractions being formed in $\mathbb R$ and then cast to $\mathbb C$, one has
--   $$\int_{\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta}\ \int_{\Omega_K}F_{m,x,R}(z)\,d\nu_{Z_K}(z)\,dx\;=\;\Lambda\Big(R\prod_{i\in T}A_i+\sum_{p\in T}\big(c_1(p)B_p+c_2(p)A_p\big)\prod_{i\in T\setminus\{p\}}A_i\Big)+\kappa_0\prod_{i\in T}A_i.$$
--
--   Thus $\Lambda,\kappa_0,c_1,c_2$ are uniform in the word $(k_\bullet,j_\bullet)$, in the family $\mathrm{fam}$, in the member $m$ of the slot family and in $R$, whereas $R_0$ may depend on $(k_\bullet,j_\bullet)$ and on $\mathrm{fam}$; the dependence of the right-hand side on $R$ is affine.
--
--   This is the explicit evaluation, on the ground field and over a whole slot family at once, of the truncated unipotent contribution to the adelic trace formula for $\mathrm{GL}_2$: the unipotent part of the kernel of a factorisable Hecke test function, folded against an idele class character over a fundamental domain for the centre and integrated over the canonical truncation domain of the slab $\mathrm{ideleNorm}(\det)\in[\alpha,\beta]$, is a linear polynomial in the truncation parameter $R$ whose coefficients are products of explicit local moment factors indexed by the Hecke words. It is the untwisted counterpart of the unramified comparison theorem [`AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram`](thm.html#AutomorphicForm.exists_forall_setIntegral_finsum_unipotentCell_sub_indicator_constantTerm_eq_weighted_moments_unram), and it feeds the summation over slot families in [`AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add`](thm.html#AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_mem_slotIndex_integrableOn_and_setIntegral_unipotentCell_eq_weighted_moments_self.lean

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
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_forall_mem_slotIndex_integrableOn_and_setIntegral_unipotentCell_eq_weighted_moments_self
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (hΦKs : ΦK ⊆
      {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦK : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range ΦK
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξKc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξKt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L)),
      ∀ (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K),
        (∀ v ∈ T, Irreducible (ϖKs v)) →
      ∀ (hϖKs0 : ∀ v ∈ T,
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
        (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
        (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K)),
        (∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
          HeckeIntegralSeam.IsHeckeCosetSystem
            (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
            (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v)) →
      ∀ (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K)),
        (∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
          algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
            (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) →
      ∃ Λ κ₀ : ℂ, ∃ c₁ c₂ : HeightOneSpectrum (𝓞 K) → ℂ,
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ),
      ∀ fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ,
        (∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          IsBiInvariantUnder K (principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K) (fam m) ∧
          IsArchBiFinite K tysK (fam m) ∧
          IsArchTestFactor K faK ∧
          (∀ v ∈ SK, IsLocalTestFn K v (fSK v)) ∧
          ∃ ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ,
            IsFinTestFactor K ff ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∀ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
                ff h = ∏ v ∈ SK ∪ T,
                  (if hv : v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
                      ∑ ι : Fin ((m v hv) 0) → Fin (nKs v),
                        (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                          (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ (m v hv) 1)⁻¹ * x)
                    else fSK v) (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
            (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
              (∃ v ∉ SK ∪ T, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) →
                ff h = 0) ∧
            ∀ g, fam m g = faK (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)
        ) →
      ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
        (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
        IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK))
          (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
        (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K (fam m) x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 = 1},
                  fam m (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) =
        Λ * ((R : ℂ) *
          ∏ i : T,
            ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                    Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
              ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                  Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1) +
          ∑ p : T,
            (c₁ p.1 *
                ((1 + (-1 : ℂ) ^ (m p.1 p.2) 0) * (4 * (HeckeEigensystem.cNorm p.1 *
                    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m p.1 p.2) 0 / 2) *
                  ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                      Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m p.1 p.2) 1) +
                c₂ p.1 *
                ((1 + (-1 : ℂ) ^ (m p.1 p.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm p.1 *
                    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m p.1 p.2) 0 / 2) *
                  ((∏ n ∈ Finset.range ((m p.1 p.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                  ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K p.1),
                      Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m p.1 p.2) 1)) *
              ∏ i ∈ Finset.univ.erase p,
                ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
                    ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                        Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
                  ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
                  ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                      Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1)) +
        κ₀ * ∏ i : T,
          ((1 + (-1 : ℂ) ^ (m i.1 i.2) 0) / 2 * (4 * (HeckeEigensystem.cNorm i.1 *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                  Subgroup.mem_top _⟩ : ℂˣ) : ℂ))) ^ ((m i.1 i.2) 0 / 2) *
            ((∏ n ∈ Finset.range ((m i.1 i.2) 0 / 2), (2 * (n : ℝ) + 1) / (2 * n + 2) : ℝ) : ℂ) *
            ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K i.1),
                Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ^ (m i.1 i.2) 1) := by sorry
