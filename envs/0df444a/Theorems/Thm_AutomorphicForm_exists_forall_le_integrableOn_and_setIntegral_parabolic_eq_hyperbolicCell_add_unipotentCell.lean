-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell
-- name    : AutomorphicForm.exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/28fa29b2-bec1-5cfd-a9e8-76940117d1f8
-- title:
--   Truncated parabolic term splits into hyperbolic and unipotent cells
-- statement:
--   Let $K$ be a number field, and write $\mathbb{A}_K$ for its adele ring and $G(\mathbb{A}_K) = \mathrm{GL}_2(\mathbb{A}_K)$ for `AdelicGL2 (𝓞 K) K`. Throughout, $\mathrm{GL}_2(K)$ is embedded in $G(\mathbb{A}_K)$ by [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15), and [`AutomorphicForm.centralScalar`](def/AutomorphicForm_AdelicLsXi.html#L18) sends an idele unit $z$ to the central scalar matrix $z\cdot 1$.
--
--   The data and hypotheses are as follows.
--
--   *Slab and global fundamental domain.* Real numbers $\alpha,\beta$ with $0 < \alpha$ and $\alpha < \beta$; a set $\Phi_K \subseteq G(\mathbb{A}_K)$ contained in the determinant slab $\{g : \ \mathrm{ideleNorm}_K(\det g) \in [\alpha,\beta]\}$, where [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) is the module of the multiplication action on $\mathbb{A}_K$ (the `distribHaarChar` value, viewed as a real number); the hypothesis `hΦK` states that $\Phi_K$ is a fundamental domain for the range of [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) acting on $G(\mathbb{A}_K)$, with respect to the adelic Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` (for the Borel structure `glBorel`) restricted to that slab.
--
--   *Centre.* A measurable space and Borel space structure on the idele units $\mathbb{A}_K^\times$, a Haar measure $\nu_{Z,K}$ on $\mathbb{A}_K^\times$, and a set $\Omega_K \subseteq \mathbb{A}_K^\times$ which, by `hΩK`, is a fundamental domain for the range of $K^\times \to \mathbb{A}_K^\times$ with respect to $\nu_{Z,K}$.
--
--   *Central character.* A homomorphism $\xi$ from the full subgroup $\top \le \mathbb{A}_K^\times$ to $\mathbb{C}^\times$ such that $z \mapsto \xi(z)$ is continuous as a complex-valued function (`hξc`) and $\xi(z)=1$ for every $z$ in the image of $K^\times$ (`hξt`).
--
--   *Test function.* A function $f : G(\mathbb{A}_K) \to \mathbb{C}$ satisfying `IsFactorizableTestFn K f`, that is, $f(g) = f_\infty(\mathrm{glArch}\,g)\, f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for some $f_\infty$ on $\mathrm{GL}_2$ of the infinite adeles which is compactly supported and of the form $\Phi \circ \mathrm{archEntries}$ with $\Phi$ smooth on the matrix mixed space, and some locally constant, compactly supported $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adeles.
--
--   Three kernels occur, all defined as sums with finite support over the indicated set of $\gamma$, of $f(x^{-1}\gamma y)$: the full kernel $K_f(x,y) = \sum_{\gamma \in \mathrm{GL}_2(K)} f(x^{-1}\gamma y)$ (`adelicKernel`), its hyperbolic part $K_f^{\mathrm{hyp}}$, where $\gamma$ runs over `hyperbolicCell K` (matrices of hyperbolic type), and its unipotent part $K_f^{\mathrm{unip}}$, where $\gamma$ runs over `unipotentCell K`.
--
--   The truncation uses the constant term [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47): for a function $h$ on $G(\mathbb{A}_K)$ it is $g \mapsto \int h(u(t)g)\,d\mu(t)$, where $u(t) =$ `unipotentGL2 t` is the unipotent matrix $\begin{pmatrix}1&t\\0&1\end{pmatrix}$ and $\mu$ is the measure component of `productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, namely the adelic additive Haar measure on $\mathbb{A}_K$ conditioned on the box `adelicBox K` (Minkowski fundamental domain at the infinite places times the integral finite adeles), taken with the Borel structure `adeleBorel` on $\mathbb{A}_K$. The cutoff set is `highSet (adelicHeight K) (Real.exp R)` $= \{g : e^{R} < H(g)\}$, with $H$ the adelic height (product of the archimedean height with multiplicities and the finite height).
--
--   Finally, the outer domain of integration is `canonicalTruncationDomain K α β`, the set component extracted from the canonically chosen truncation datum for $(K,\alpha,\beta)$ (empty if no such datum exists).
--
--   Conclusion: there exists $R_0 \in \mathbb{R}$ such that for every real $R \ge R_0$ the following five assertions hold.
--
--   (1) For every $x \in G(\mathbb{A}_K)$, the function
--   $$z \mapsto \xi(z)\Bigl(K_f^{\mathrm{hyp}}(x, z x) - \mathbf 1_{\{H > e^{R}\}}(z x)\cdot \bigl(\textstyle\sum_{\gamma}\,f(x^{-1}\gamma\,\cdot)\bigr)_N(z x)\Bigr)$$
--   is integrable on $\Omega_K$ with respect to $\nu_{Z,K}$, where the inner sum runs with finite support over $\{\gamma \in \mathrm{GL}_2(K) : \gamma_{10} = 0,\ \gamma_{00}/\gamma_{11} \neq 1\}$ and $(\cdot)_N$ denotes the constant term described above.
--
--   (2) The function of $x$ given by the inner integral $\int_{\Omega_K}$ of the integrand in (1) over $\nu_{Z,K}$ is integrable on `canonicalTruncationDomain K α β` with respect to `adelicGLHaar (Fin 2) (𝓞 K) K`.
--
--   (3) For every $x \in G(\mathbb{A}_K)$, the corresponding function with $K_f^{\mathrm{hyp}}$ replaced by $K_f^{\mathrm{unip}}$ and the inner sum taken over $\{\gamma \in \mathrm{GL}_2(K) : \gamma_{10} = 0,\ \gamma_{00}/\gamma_{11} = 1\}$ is integrable on $\Omega_K$ with respect to $\nu_{Z,K}$.
--
--   (4) The function of $x$ given by the inner integral over $\Omega_K$ of the integrand in (3) is integrable on `canonicalTruncationDomain K α β` with respect to `adelicGLHaar (Fin 2) (𝓞 K) K`.
--
--   (5) The identity
--   $$\int_{\Phi_0}\!\int_{\Omega_K} \xi(z)\Bigl(\bigl(K_f^{\mathrm{hyp}} + K_f^{\mathrm{unip}}\bigr)(x, z x) - \mathbf 1_{\{H > e^{R}\}}(z x)\cdot \bigl(K_f(x,\cdot)\bigr)_N(z x)\Bigr)\, d\nu_{Z,K}(z)\, dx$$
--   equals the sum of the integral of the function in (2) and the integral of the function in (4), both over $\Phi_0 =$ `canonicalTruncationDomain K α β` against `adelicGLHaar (Fin 2) (𝓞 K) K`. Thus on the left the subtracted constant term is that of the full kernel $y \mapsto K_f(x,y)$, while on the right it appears split into the constant terms of the two upper-triangular sub-sums distinguished by whether the diagonal ratio $\gamma_{00}/\gamma_{11}$ equals $1$.
--
--   This is the cell decomposition of the truncated parabolic term in the coarse geometric expansion of the Arthur–Selberg trace formula for $\mathrm{GL}_2$ over a number field: above the height cutoff the constant term of the kernel receives contributions only from upper-triangular rational elements, and these split according to the diagonal ratio, each cell being absolutely integrable over the folded truncation domain. It is used in the passage to the limit of the truncated trace ([`AutomorphicForm.exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization`](thm.html#AutomorphicForm.exists_tendsto_setIntegral_lambdaT_adelicKernel_sub_centralElliptic_sub_affine_atTop_of_isUnitFactorization)) and in the analysis of the parabolic intercept ([`AutomorphicForm.exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform`](thm.html#AutomorphicForm.exists_continuous_noAtomicMass_intercept_parabolic_sub_finrank_mul_const_mul_sum_intercept_parabolic_eq_uniform)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell.lean

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

theorem AutomorphicForm.exists_forall_le_integrableOn_and_setIntegral_parabolic_eq_hyperbolicCell_add_unipotentCell
    (K : Type) [Field K] [NumberField K]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
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
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξ ⟨z, Subgroup.mem_top z⟩ = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hff : IsFactorizableTestFn K f) :
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK))
        (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
      (∀ x : AdelicGL2 (𝓞 K) K, IntegrableOn (fun z : (AdeleRing (𝓞 K) K)ˣ =>
        ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
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
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x))) ΩK νZK) ∧
      IntegrableOn (fun x : AdelicGL2 (𝓞 K) K => (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
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
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK))
        (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) ∧
      ∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
          (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            ((AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) +
                AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x)) -
              Set.indicator
                (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
                (@AutomorphicForm.constantTerm _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                  (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                  (fun t => AutomorphicForm.unipotentGL2 t)
                  (fun y => AutomorphicForm.adelicKernel K f x y))
                (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelHyperbolicPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
              Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R))
              (@AutomorphicForm.constantTerm _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).nS _ _
                (productionPinsOf K ΦK (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
                  (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (fun y => ∑ᶠ γ ∈ {γ : GL (Fin 2) K |
                  (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
                    (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1},
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) +
      (∫ x in AutomorphicForm.canonicalTruncationDomain K α β,
            (∫ z in ΩK, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
            (AutomorphicForm.adelicKernelUnipotentPart K f x (AutomorphicForm.centralScalar (𝓞 K) K z * x) -
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
                  f (x⁻¹ * AutomorphicForm.globalPoints (𝓞 K) K γ * y)))
              (AutomorphicForm.centralScalar (𝓞 K) K z * x)) ∂νZK)
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) := by sorry
