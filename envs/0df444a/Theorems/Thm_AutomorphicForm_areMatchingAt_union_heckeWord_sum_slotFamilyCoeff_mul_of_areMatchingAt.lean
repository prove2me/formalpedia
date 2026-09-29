-- Prove2me | Theorems.Thm_AutomorphicForm_areMatchingAt_union_heckeWord_sum_slotFamilyCoeff_mul_of_areMatchingAt
-- name    : AutomorphicForm.areMatchingAt_union_heckeWord_sum_slotFamilyCoeff_mul_of_areMatchingAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/23e375a2-498e-5376-b693-f878bef236a4
-- title:
--   Hecke words and slot-family combinations are matching at S_K∪ T
-- statement:
--   Let $K\subseteq L$ be number fields with $L/K$ finite Galois, let $\sigma$ be an element of $\mathrm{Gal}(L/K)$ such that every $\tau$ lies in the subgroup of integer powers of $\sigma^{-1}$, and let $[L:K]$ be prime. Let $S_K$ be a finite set of finite places of $K$ such that every finite place $w$ of $L$ whose restriction to $K$ lies outside $S_K$ has ramification index $1$. Fix an archimedean factor $\varphi_a$ on $\mathrm{GL}_2$ of the infinite adeles of $L$, semi-local factors $\varphi_{S,v}$ on $\mathrm{GL}_2(L\otimes_K K_v)$, an archimedean factor $f_a$ and local factors $f_{S,v}$ on the $K$-side, and functions $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_L)$, $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ which are matching at $\sigma^{-1}$ and $S_K$ (i.e. admit a semi-local, resp. unit, factorisation at $S_K$ whose archimedean factors have matching twisted and ordinary orbital integrals, and likewise at each $v\in S_K$), and assume moreover that $\varphi$ admits a semi-local factorisation at $S_K$ with factors $\varphi_a,\varphi_{S,v}$ and some $\varphi_f$, and $f$ a unit factorisation at $S_K$ with factors $f_a, f_{S,v}$ and some $f_f$. The assertion is then: for every finite set $T$ of finite places of $K$ disjoint from $S_K$ with $|T|\ge 2$; every choice, for each $v$, of a place $w_v$ of $L$ above $v$ and of elements $\varpi_{w_v}$, $\varpi_v$ of the valuation rings of $L_{w_v}$, $K_v$ which are irreducible with nonzero image in the completion for $v\in T$; every families $(r_{v,i})_{i<n_v}$ in $\mathrm{GL}_2(L_{w_v})$ and $(r^K_{v,i})_{i<n^K_v}$ in $\mathrm{GL}_2(K_v)$ which, for $v\in T$, are Hecke coset systems for the double coset of $\mathrm{diag}(\varpi,1)$ modulo the integral subgroup (each representative lies in the double coset, every element of it is congruent to one of them modulo the subgroup, and the induced map to the coset space is injective); every $z_{w_v}$, $z_v$ equal to the scalar matrices $\varpi_{w_v}\cdot 1$, $\varpi_v\cdot 1$ for $v\in T$; all exponents $k,j$; every $\varphi_L$ and $\varphi_f$ giving a semi-local factorisation at $S_K\cup T$ of $\varphi_L$ with archimedean factor $\varphi_a$, semi-local factor $\varphi_{S,v}$ at $v\in S_K$ and, at $v\in T$, the Hecke-word factor $x\mapsto\sum_{\iota:\,\mathrm{Fin}(k_v)\to\mathrm{Fin}(n_v)}\mathbf{1}_{\mathcal{O}\text{-integral set}}\big(\mathrm{sl}_v(\mathrm{emb}_{w_v}(\prod_m r_{v,\iota(m)}\cdot z_{w_v}^{\,j_v}))^{-1}x\big)$, where $\mathrm{emb}_{w_v}$ is the embedding of $\mathrm{GL}_2(L_{w_v})$ into $\mathrm{GL}_2$ of the finite adeles of $L$ and $\mathrm{sl}_v$ the semi-local component map; and every family $(\mathrm{fam}_m)$ indexed by the functions $m$ assigning to each $v\in T$ an element of $\mathbb{N}^{\mathrm{Fin}\,2}$, such that for each $m$ in the index set $T.\mathrm{pi}$ of supports of the slot words, $f_a$ is an archimedean test factor, each $f_{S,v}$ ($v\in S_K$) is locally constant with compact support, and there is a locally constant compactly supported $f_f$ which vanishes when some component outside $S_K\cup T$ is non-integral, equals the product over $v\in S_K\cup T$ of $f_{S,v}$ (for $v\in S_K$) and of the analogous Hecke-word factor with word length $m_v(0)$, representatives $r^K_{v,i}$ and power $z_v^{m_v(1)}$ (for $v\in T$) when all components outside $S_K\cup T$ are integral, and with $\mathrm{fam}_m(g)=f_a(\text{arch part})\cdot f_f(\text{finite part})$: then $\varphi_L$ and $x\mapsto\sum_m c_m\,\mathrm{fam}_m(x)$ are matching at $\sigma^{-1}$ and $S_K\cup T$, where $c_m$ is the product over $v\in T$ of the coefficient of $m_v$ in the slot word at $v$ times $N(v)^{m_v(1)}$ divided by $N(w_v)^{j_v}$.
--
--   This is the global form of the fundamental lemma for spherical Hecke operators in cyclic base change of prime degree for $\mathrm{GL}(2)$, made explicit on Hecke words: a test function on $\mathrm{GL}_2(\mathbb{A}_L)$ carrying a word in the Hecke operators at the places $w_v$, $v\in T$, is matched by the explicit linear combination, with the slot-family coefficients, of the corresponding words on the $K$-side. It is used in the comparison of twisted and ordinary trace contributions, where the Hecke-word sums appear in the cut traces and geometric remainders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_areMatchingAt_union_heckeWord_sum_slotFamilyCoeff_mul_of_areMatchingAt.lean

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

theorem AutomorphicForm.areMatchingAt_union_heckeWord_sum_slotFamilyCoeff_mul_of_areMatchingAt
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ.symm)
    (hdeg : (Module.finrank K L).Prime)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ w : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w ∉ SK →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w).asIdeal w.asIdeal = 1)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (φS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hm : AreMatchingAt K L σ.symm SK φ f)
    (hφfac : ∃ φf, IsSemiLocalFactorization K L SK φ φa φf φS)
    (hffac : ∃ ff, IsUnitFactorization K SK f faK ff fSK) :
    ∀ (T : Finset (HeightOneSpectrum (𝓞 K))), Disjoint T SK → 2 ≤ T.card →
      ∀ (ws : ∀ v : HeightOneSpectrum (𝓞 K), v.Extension (𝓞 L))
        (ϖs : ∀ v : HeightOneSpectrum (𝓞 K), (ws v).1.adicCompletionIntegers L),
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
      ∀ (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
        (φL : AdelicGL2 (𝓞 L) L → ℂ)
        (φf : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
        IsSemiLocalFactorization K L (SK ∪ T) φL φa φf
          (fun v => if v ∈ T then fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
            ∑ ι : Fin (ks v) → Fin (ns v),
              (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
                ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L (ws v).1
                  ((List.ofFn fun m => rTs v (ι m)).prod * zs v ^ js v)))⁻¹ * x)
            else φS v) →
      ∀ fam : ((u : HeightOneSpectrum (𝓞 K)) → u ∈ T → (Fin 2 →₀ ℕ)) → AdelicGL2 (𝓞 K) K → ℂ,
        (∀ m ∈ SatakeCombination.slotIndex K L ws ks js T,
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
      AreMatchingAt K L σ.symm (SK ∪ T) φL
        (fun x => ∑ m ∈ SatakeCombination.slotIndex K L ws ks js T,
          SatakeCombination.slotFamilyCoeff K L ws ks js T m * fam m x) := by sorry
