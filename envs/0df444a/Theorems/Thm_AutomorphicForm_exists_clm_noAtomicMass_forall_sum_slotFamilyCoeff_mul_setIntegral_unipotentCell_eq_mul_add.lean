-- Prove2me | Theorems.Thm_AutomorphicForm_exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add
-- name    : AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/3c156607-f0d2-5e0c-92d7-2173af728986
-- title:
--   Affine shape of base-changed unipotent terms along Hecke words
-- statement:
--   Fix number fields $K$ and $L$ with $L/K$ a finite Galois extension, and an element $\sigma \in \mathrm{Gal}(L/K)$. Fix reals $\alpha, \beta$ with $0 < \alpha$ and $\alpha < \beta$, finite sets of finite places $S_K \subseteq \mathrm{Spec}^1(\mathcal O_K)$ and $S_L \subseteq \mathrm{Spec}^1(\mathcal O_L)$, and a homomorphism $\xi_L : (\mathbb A_L^\times)^{\top} \to \mathbb C^\times$ on the full subgroup of the idele units of $L$.
--
--   Test data on the $K$-side: a function $f_{a,K}$ on $GL_2$ of the infinite adeles of $K$, and for each finite place $v$ of $K$ a function $f_{S_K,v}$ on $GL_2(K_v)$.
--
--   Table space: a set $X$ of functions $\mathrm{Spec}^1(\mathcal O_L) \to \mathbb C \times \mathbb C$, assumed compact (`hXc`), and assumed (`hX`) to contain the set of all $x$ such that $x_w = 0$ for every $w \in S_L$ and such that, for every $w \notin S_L$: the second coordinate satisfies $(x_w)_2 = \mathrm{absNorm}(w)\cdot \xi_L(\det \mathrm{heckeGen}_w)$, where `HeckeEigensystem.cNorm` $w$ is the absolute norm of $w$ viewed in $\mathbb C$ and $\mathrm{heckeGen}_w$ is the adelic Hecke generator at $w$; the first coordinate satisfies $\lVert (x_w)_1\rVert \le (\mathrm{absNorm}(w)+1)\sqrt{\lVert \xi_L(\det\mathrm{heckeGen}_w)\rVert}$; and $\overline{(x_w)_1} = \overline{(x_w)_2}/\lVert (x_w)_2\rVert \cdot (x_w)_1$.
--
--   Global geometric data on the $K$-side: a set $\Phi_K \subseteq GL_2(\mathbb A_K)$ contained in the slab $\{g : \lVert \det g\rVert_{\mathbb A_K} \in [\alpha,\beta]\}$ (`hΦKs`, the idele norm being Tate's `ideleNorm`, the module of the distributive Haar character), and assumed (`hΦK`) to be a fundamental domain for the range of the global-points homomorphism $GL_2(K) \to GL_2(\mathbb A_K)$ acting on the adelic Haar measure of $GL_2$ restricted to that slab. Central data: a measurable space and Borel space structure on $(\mathbb A_K)^\times$, a Haar measure $\nu_{Z_K}$ on $(\mathbb A_K)^\times$, and a set $\Omega_K$ assumed (`hΩK`) to be a fundamental domain for the range of $K^\times \to (\mathbb A_K)^\times$ with respect to $\nu_{Z_K}$.
--
--   Character data on the $K$-side: a homomorphism $\xi_K : (\mathbb A_K^\times)^{\top} \to \mathbb C^\times$ with three hypotheses: $z \mapsto \xi_K(z)$ is continuous (`hξKc`); $\xi_K$ is trivial on the image of $K^\times$ (`hξKt`); and $\xi_K$ composed with the idelic norm of the genuine base change $\mathbb A_K \to \mathbb A_L$ equals $\xi_L$ (`hξKN`). Level and type data: an ideal $N' \subseteq \mathcal O_K$ whose prime divisors all lie in $S_K$ (`hN'`), and an archimedean type family $\mathrm{tys}_K$ for $K$ (a cardinality function on infinite places together with, at each place, that many archimedean representation types).
--
--   Under these hypotheses the following holds for every finite set $T$ of finite places of $K$ that is disjoint from $S_K$, has $\lvert T\rvert \ge 2$, and is such that no place $w$ of $L$ lying under-$K$ over a $v \in T$ belongs to $S_L$; for every assignment $v \mapsto w_v$ of an extension of $v$ to $\mathcal O_L$ and every function $w' : \mathrm{Spec}^1(\mathcal O_K) \to \mathrm{Spec}^1(\mathcal O_L)$ with $(w'_v)$'s ideal equal to $\sigma^{-1} \cdot (w_v)$'s ideal for all $v \in T$; for every family $\varpi_v$ of elements of the valuation rings $\mathcal O_{K_v}$ that are irreducible for $v \in T$ and whose images in $K_v$ are non-zero for $v \in T$; for every family of naturals $n_v$ and representatives $r_v : \mathrm{Fin}(n_v) \to GL_2(K_v)$ such that, for each $v \in T$, $r_v$ is a Hecke coset system for the integral subgroup $GL_2(\mathcal O_{K_v})$ (the image of $GL_2$ of the valuation ring in $GL_2(K_v)$) and the diagonal element $\mathrm{diag}(\varpi_v,1)$ — that is, each $r_v(i)$ lies in the double coset, every element of the double coset is congruent modulo the subgroup to some $r_v(i)$, and the induced map to the quotient is injective; and for every family $z_v \in GL_2(K_v)$ whose matrix, for $v \in T$, is $\varpi_v$ times the identity.
--
--   The conclusion asserts the existence of two continuous $\mathbb C$-linear functionals $\nu', \mu' : C(X,\mathbb C) \to \mathbb C$ with the following two properties.
--
--   First, $\mu'$ has no atomic mass in the coordinates $w'_v$, $v \in T$: for every $\tau : \mathrm{Spec}^1(\mathcal O_K) \to \mathbb C \times \mathbb C$ and every $\varepsilon > 0$ there are sets $U_v \subseteq \mathbb C\times\mathbb C$ with $U_v$ open and $\tau_v \in U_v$ for all $v \in T$, such that every $g \in C(X,\mathbb C)$ which vanishes at every $y \in X$ for which $y(w'_v) \notin U_v$ for some $v \in T$ and which satisfies $\lVert g(y)\rVert \le 1$ everywhere has $\lVert \mu'(g)\rVert < \varepsilon$.
--
--   Second, for all pairs of exponent functions $k, j : \mathrm{Spec}^1(\mathcal O_K) \to \mathbb N$ and every family $\mathrm{fam}$ assigning to each slot index $m$ (a function giving, for $v \in T$, an element of $\mathrm{Fin}\,2 \to_{\mathrm f} \mathbb N$) a function $\mathrm{fam}(m)$ on $GL_2(\mathbb A_K)$, subject to the hypothesis that for each $m$ in the slot index set $\mathrm{slotIndex}\,K\,L\,w\,k\,j\,T$ (the $T$-indexed product of the supports of the slot words) the function $\mathrm{fam}(m)$ is: bi-invariant under the intersection of the principal level subgroup of $N'$ with the finite adelic subgroup (the kernel of the archimedean projection), archimedean bi-finite of type $\mathrm{tys}_K$ (its inverse-twist lying in the archimedean cut submodule and itself in the archimedean dual cut submodule), with $f_{a,K}$ an archimedean test factor (smooth in the archimedean matrix entries and of compact support), with each $f_{S_K,v}$, $v \in S_K$, a local test function (locally constant of compact support), and factorised as $\mathrm{fam}(m)(g) = f_{a,K}(g_\infty)\, f\!f(g_{\mathrm{fin}})$ for some finite test factor $f\!f$ (locally constant of compact support) which vanishes whenever some component of $g_{\mathrm{fin}}$ outside $S_K \cup T$ fails to be integral, and which on $g_{\mathrm{fin}}$ with all components outside $S_K \cup T$ integral equals the product over $v \in S_K \cup T$ of: at $v \in T$, the function $x \mapsto \sum_{\iota : \mathrm{Fin}(m_v(0)) \to \mathrm{Fin}(n_v)} \mathbf 1_{GL_2(\mathcal O_{K_v})}\big( (\prod_i r_v(\iota_i)\, z_v^{m_v(1)})^{-1} x \big)$, and at $v \in S_K$, $f_{S_K,v}$, evaluated at the $v$-component — the following holds: there exists $R_0 \in \mathbb R$ such that for every $R \ge R_0$ both of the following hold.
--
--   (a) Integrability: for every $m$ in the slot index set, and writing $\mathcal K_m(x,z)$ for
--   $$\xi_K(z)\Big(\mathrm{adelicKernelUnipotentPart}_K(\mathrm{fam}(m))(x, z\cdot x) - \mathbf 1_{\{H > e^R\}}\big(\mathrm{constantTerm}\big)(z\cdot x)\Big),$$
--   where $\mathrm{adelicKernelUnipotentPart}_K(f)(x,y) = \sum^{\mathrm f}_{\gamma \in \mathrm{unipotentCell}(K)} f(x^{-1}\gamma y)$ is the finsum over unipotent-type $\gamma \in GL_2(K)$, $z \cdot x$ denotes the central scalar $z$ times $x$, $H$ is the adelic height, and the constant term is the integral over the adele ring of $\mathbb A_K$-translates by the unipotent matrices $\mathrm{unipotentGL2}(t) = \begin{pmatrix}1&t\\0&1\end{pmatrix}$ of the function $y \mapsto \sum^{\mathrm f}_{\gamma}\mathrm{fam}(m)(x^{-1}\gamma y)$ summed over the $\gamma \in GL_2(K)$ with lower-left entry $0$ and ratio of diagonal entries $1$, taken with respect to the measure $\nu$ of the production pins of $\Phi_K$, the principal-level subgroups, the Hecke generators and the adelic box (the adelic additive Haar measure conditioned on the adelic box): the function $z \mapsto \mathcal K_m(x,z)$ is integrable on $\Omega_K$ with respect to $\nu_{Z_K}$ for every $x$, and the function $x \mapsto \int_{\Omega_K}\mathcal K_m(x,z)\,d\nu_{Z_K}$ is integrable on the canonical truncation domain $\mathcal D_K(\alpha,\beta)$ with respect to the adelic Haar measure of $GL_2$.
--
--   (b) The affine identity: for every $g \in C(X,\mathbb C)$ which on $X$ is given by the monomial
--   $$g(x) = \prod_{v \in T} \big(x(w'_v)_1\big)^{k_v}\Big(\mathrm{absNorm}(w'_v)^{-1}\, x(w'_v)_2\Big)^{j_v},$$
--   there is
--   $$\sum_{m \in \mathrm{slotIndex}} \mathrm{slotFamilyCoeff}\,K\,L\,w\,k\,j\,T\,m \cdot \int_{\mathcal D_K(\alpha,\beta)} \int_{\Omega_K} \mathcal K_m(x,z)\, d\nu_{Z_K}\, d\mu_{GL_2} \; = \; R\,\nu'(g) + \mu'(g),$$
--   where $\mathrm{slotFamilyCoeff}$ is the product over $v \in T$ of the slot coefficients $\mathrm{slotCoeff}\,K\,L\,w\,v\,k_v\,j_v\,(m_v)$, i.e. of the coefficient of $m_v$ in the slot word at $v$, multiplied by $\mathrm{absNorm}(v)^{m_v(1)}$ and divided by $\mathrm{absNorm}(w_v)^{j_v}$.
--
--   Thus the truncated weighted unipotent contribution attached to a Hecke word $(k,j)$ along $T$ is an affine function of the truncation parameter $R$, with slope $\nu'(g)$ and intercept $\mu'(g)$, the intercept carrying no atomic mass at the $T$-coordinates.
--
--   This is the ground-field leaf of the unipotent-term comparison in cyclic base change for $GL(2)$: it records that, after the Satake slot combination attached to a Hecke word along $T$ is applied, the truncated unipotent part of the $\xi_K$-isotypic kernel integral depends on the truncation parameter $R$ affinely, with an intercept functional that is atom-free in the coordinates indexed by the places $w'_v$ of $L$. It is used by [`AutomorphicForm.exists_continuous_noAtomicMass_integrableOn_and_unipotentTerm_sub_const_mul_sum_eq_of_areMatchingAt`](thm.html#AutomorphicForm.exists_continuous_noAtomicMass_integrableOn_and_unipotentTerm_sub_const_mul_sum_eq_of_areMatchingAt), where the $K$-side and $L$-side unipotent terms are matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add.lean

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

theorem AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (σ : L ≃ₐ[K] L)
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (X : Set (HeightOneSpectrum (𝓞 L) → ℂ × ℂ)) (hXc : IsCompact X)
    (hX : {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} ⊆ X)
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
    (hξKN : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      ξK ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
        ξL ⟨z, Subgroup.mem_top z⟩)
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (tysK : ArchTypeFamily K) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      (∀ v ∈ T, ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w = v → w ∉ SL) →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (w' : HeightOneSpectrum (𝓞 K) → HeightOneSpectrum (𝓞 L)),
        (∀ v ∈ T, (w' v).asIdeal = σ.symm • (ws v).1.asIdeal) →
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
      ∃ ν' μ' : C(X, ℂ) →L[ℂ] ℂ,
      (∀ (τ : HeightOneSpectrum (𝓞 K) → ℂ × ℂ), ∀ ε > (0 : ℝ),
        ∃ U : HeightOneSpectrum (𝓞 K) → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
          ∀ g : C(X, ℂ),
            (∀ y : X, (∃ v ∈ T, (y : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) →
            (∀ y, ‖g y‖ ≤ 1) → ‖μ' g‖ < ε) ∧
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
      (∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
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
          (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K)) ∧
      ∀ g : C(X, ℂ),
        (∀ x : X, g x = ∏ v ∈ T,
          ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).1 ^ ks v *
            ((HeckeEigensystem.cNorm (w' v))⁻¹ *
              ((x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ) (w' v)).2) ^ js v) →
        ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m *
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
        (R : ℂ) * ν' g + μ' g := by sorry
