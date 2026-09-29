-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one
-- name    : AutomorphicForm.setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/1d6fd837-96f5-5f58-84a0-99f4548b0e34
-- title:
--   Vanishing of the unipotent fold against a character ramified on T
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ a finite Galois extension, let $0<\alpha<\beta$ be reals, let $S_K$ be a finite set of finite places of $K$, let $f_{a,K}$ be a function on $GL_2$ of the infinite adeles and $f_{S_K,v}$ local functions on $GL_2(K_v)$, and let $\Phi_K\subseteq GL_2(\mathbb{A}_K)$ be contained in the slab where the idele norm of the determinant lies in $[\alpha,\beta]$ and be a fundamental domain for the image of $GL_2(K)$ acting on that slab for the adelic Haar measure restricted to it. Let $\nu_{Z_K}$ be a Haar measure on $\mathbb{A}_K^\times$ with $\Omega_K$ a fundamental domain for the image of $K^\times$, and let $\xi_K$ be a homomorphism from the full unit group (as the top subgroup) to $\mathbb{C}^\times$ which is continuous as a complex-valued function and trivial on principal ideles. Let $N'$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$, and let $\mathrm{tys}_K$ be an archimedean type family for $K$. Then for every finite set $T$ of finite places disjoint from $S_K$, every choice of extensions $w_v$ of each $v$ to $\mathcal{O}_L$, every family $\varpi_{K,v}$ of elements of the local integers that are irreducible and nonzero in $K_v$ for $v\in T$, every system of coset representatives $r_{K,v}$ of $GL_2(\mathcal{O}_v)\,\mathrm{diag}(\varpi_{K,v},1)\,GL_2(\mathcal{O}_v)$ modulo $GL_2(\mathcal{O}_v)$ (in the sense that each representative lies in the double coset, every element of the double coset is congruent to one of them modulo $GL_2(\mathcal{O}_v)$, and the induced map to the coset space is injective), and every family $z_{K,v}$ whose matrix at $v\in T$ is $\varpi_{K,v}$ times the identity: if $\xi_K$ is nontrivial on some local unit idele at a place of $T$, i.e. there are $v\in T$ and $t\in K_v^\times$ with $|t|_v=1$ and $\xi_K$ of the idele equal to $t$ at $v$ and $1$ elsewhere not equal to $1$, then for all exponent functions $k_s,j_s$ and every family $\mathrm{fam}$ indexed by the slot index set $\mathrm{SatakeCombination.slotIndex}\ K\ L\ w_s\ k_s\ j_s\ T$ such that each member $\mathrm{fam}(m)$ is bi-invariant under $\mathrm{principalLevel}\ N'$ intersected with the kernel of the archimedean projection, is archimedean bi-finite for $\mathrm{tys}_K$, with $f_{a,K}$ an archimedean test factor and each $f_{S_K,v}$ ($v\in S_K$) a locally constant compactly supported local function, and factorises as $\mathrm{fam}(m)(g)=f_{a,K}(g_\infty)\cdot f_f(g_f)$ for a locally constant compactly supported $f_f$ which vanishes when some component outside $S_K\cup T$ is non-integral and otherwise equals the product over $v\in S_K\cup T$ of $f_{S_K,v}$ for $v\notin T$ and, for $v\in T$, of the sum over maps $\iota$ from $\mathrm{Fin}(m(v)_0)$ to the representative index set of the integral-set indicator evaluated at $((\prod_\iota r_{K,v})\,z_{K,v}^{m(v)_1})^{-1}x$: for every $m$ in the slot index set, every real $R$ and every $x\in GL_2(\mathbb{A}_K)$, the integral over $z\in\Omega_K$ of $\xi_K(z)$ times the difference between the unipotent kernel fold $\sum_{\gamma}\mathrm{fam}(m)(x^{-1}\gamma(zx))$ over unipotent-type $\gamma\in GL_2(K)$ and the indicator of the set where the adelic height exceeds $e^R$ times the constant term (the integral over the adelic box conditional measure of the fold along unipotent matrices, summed over $\gamma\in GL_2(K)$ with lower-left entry $0$ and ratio of diagonal entries $1$), both evaluated at $z x$ via the central scalar, vanishes.
--
--   This is the ramified branch in the analysis of the unipotent contribution to the adelic trace formula for $GL_2$ over the ground field: when the idele class character $\xi_K$ is nontrivial on the local units at a place of the Hecke set $T$, the truncated unipotent fold integrates to zero against $\xi_K$. It feeds the ground-field leaf [`AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add`](thm.html#AutomorphicForm.exists_clm_noAtomicMass_forall_sum_slotFamilyCoeff_mul_setIntegral_unipotentCell_eq_mul_add).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one.lean

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

theorem AutomorphicForm.setIntegral_unipotentCell_fold_eq_zero_of_exists_localUnit_apply_ne_one
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
      (∃ v ∈ T, ∃ t : (v.adicCompletion K)ˣ, Valued.v (t : v.adicCompletion K) = 1 ∧
        ξK ⟨Units.map (finIncl (𝓞 K) K) (localUnit (𝓞 K) K v t), Subgroup.mem_top _⟩ ≠ 1) →
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
      ∀ m ∈ SatakeCombination.slotIndex K L ws ks js T, ∀ (R : ℝ) (x : AdelicGL2 (𝓞 K) K),
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
          (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK) = 0 := by sorry
