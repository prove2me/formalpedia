-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital
-- name    : AutomorphicForm.setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/480b7eeb-0be8-522b-a0c8-cbb3cebeabd5
-- title:
--   Unfolding a truncated hyperbolic constant term over the centre
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L/K$ Galois, $\sigma \in \mathrm{Gal}(L/K)$, and the hypothesis `hgen` asks that every $\tau \in \mathrm{Gal}(L/K)$ lie in the subgroup of integral powers of $\sigma$. On the idele unit group $(\mathbb A_L)^{\times}$ a Haar measure $\nu_{Z_L}$ is fixed, together with a set $\Omega_L$ which, by the hypothesis `hΩL`, is a fundamental domain for the action of the image of $L^{\times}$ (the range of the map induced on units by $L \to \mathbb A_L$) with respect to $\nu_{Z_L}$. The datum $D$ is an [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb A_L$, each automorphism continuous, and each compatible with the corresponding field automorphism on the image of $L$.
--
--   The central character data are a homomorphism $\xi_L$ from the full subgroup $\top \le (\mathbb A_L)^{\times}$ to $\mathbb C^{\times}$, with `hξc` asserting that $z \mapsto \xi_L(z) \in \mathbb C$ is continuous and `hξt` asserting that $\xi_L$ is trivial on principal ideles.
--
--   The hyperbolic datum is $\delta_0 \in \mathrm{GL}_2(L)$ whose $(1,0)$ and $(0,1)$ entries vanish (`hδ₀u`, `hδ₀l`), subject to the regularity condition `hreg`: $N_{L/K}\big((\delta_0)_{00}/(\delta_0)_{11}\big) \neq 1$. Two further pieces of group-theoretic bookkeeping are given: a set $I \subseteq \mathrm{GL}_2(L)$ characterised by `hI`, namely $\delta \in I$ if and only if there is $g \in \mathrm{GL}_2(L)$ with $\delta_0^{-1}\big(g^{-1}\,\delta\,\sigma(g)\big)$ central, where $\sigma$ acts entrywise through `Matrix.GeneralLinearGroup.map`; and a subgroup $\Lambda \le \mathrm{GL}_2(L)$ characterised by `hΛ`, namely $\gamma \in \Lambda$ if and only if $\delta_0^{-1}\big(\gamma\,\delta_0\,\sigma(\gamma)^{-1}\big)$ is central. A countable index type $\iota$ and a family $r : \iota \to \mathrm{GL}_2(L)$ are given with `hr`: for every $\gamma$ there is a unique $i$ with $(r\,i)^{-1}\gamma \in \Lambda$.
--
--   The torus data are a subgroup $\Lambda' \le \mathrm{GL}_2(L)$ characterised by `hΛ'`, namely $a \in \Lambda'$ if and only if $a$ is diagonal (entries $(1,0)$ and $(0,1)$ zero) and $a_{00}/a_{11}$ lies in the image of $K$ in $L$; a countable type $\kappa$; and a family $ra : \kappa \to \mathrm{GL}_2(L)$ of diagonal matrices (`hrad`) which by `hra` represents the $\Lambda'$-cosets of diagonal matrices: for every diagonal $a$ there is a unique $j$ with $(ra\,j)^{-1}a \in \Lambda'$. Finally $\varphi : \mathrm{GL}_2(\mathbb A_L) \to \mathbb C$ is continuous with compact support (`hφc`, `hφs`), $x \in \mathrm{GL}_2(\mathbb A_L)$, $R \in \mathbb R$, and $\Phi_L$ is a set of adelic matrices which enters only as a field of the package `productionPinsOf` below.
--
--   Notation for the statement: $\iota(\gamma)$ denotes `globalPoints`, the image of $\gamma \in \mathrm{GL}_2(L)$ in $\mathrm{GL}_2(\mathbb A_L)$; $c(z)$ denotes `centralScalar`, the scalar matrix attached to an idele unit $z$; $n(s) = \begin{pmatrix} 1 & s \\ 0 & 1\end{pmatrix}$ is `unipotentGL2`; $\sigma_D$ is `sigmaAdelicAct`, the entrywise action on $\mathrm{GL}_2(\mathbb A_L)$ of the ring automorphism $D.\mathrm{act}\,\sigma$; $w = \iota\big(\begin{smallmatrix} 0&1\\1&0\end{smallmatrix}\big)$ is `adelicWeyl`; $\mu_{\mathbb A}$ is `adelicAddHaar` on $\mathbb A_L$; $H$ is `adelicHeight`, the product of the archimedean and finite adelic heights; and $y_j = \iota(ra\,j)^{-1}x$.
--
--   The truncated constant term occurring in the statement is formed with the measurable space and measure fields of `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)`: its `nS` field is the Borel structure `adeleBorel` on $\mathbb A_L$ and its `ν` field is the conditional probability measure of $\mu_{\mathbb A}$ on the box `adelicBox L`, written $\nu_{\mathrm{box}}$ below (the other fields of the package — the set $\Phi_L$, the level subgroups and the Hecke generators — do not occur in these two fields). With
--   $$\mathrm{CT}(g) \;=\; \int_{\mathbb A_L} \ \sum^{\mathrm f}_{\delta \in \{\gamma \,:\, \gamma_{10}=0 \ \wedge\ \gamma \in I\}} \varphi\big(x^{-1}\,\iota(\delta)\,\sigma_D(n(t)\,g)\big)\, \mathrm d\nu_{\mathrm{box}}(t),$$
--   where $\sum^{\mathrm f}$ is the `finsum` over the indicated set, the integrand appearing on the left of the last conjunct is $z \mapsto \xi_L(z)\cdot \mathbf 1[\,e^R < H(c(z)x)\,]\,\mathrm{CT}(c(z)x)$, the indicator being that of `highSet` $H$ $e^R = \{g : e^R < H(g)\}$ applied to the function $\mathrm{CT}$ at the point $c(z)x$.
--
--   The conclusion is a conjunction of four assertions.
--
--   First, finiteness of a sum of upper integrals:
--   $$\sum_{j \in \kappa} \Big( \int^{-}_{s \in \mathbb A_L} \int^{-}_{z} \|\xi_L(z)\|_{\mathrm e}\,\big\|\varphi\big((n(s)y_j)^{-1}\,\iota(\delta_0)\,\sigma_D\big(c(z)\,(n(s)y_j)\big)\big)\big\|_{\mathrm e}\, \mathrm d\nu_{Z_L}\,\mathrm d\mu_{\mathbb A} \;+\; \int^{-}_{s \in \mathbb A_L} \int^{-}_{z} \|\xi_L(z)\|_{\mathrm e}\,\big\|\varphi\big((w^{-1}n(s)y_j)^{-1}\,\iota(\delta_0)\,\sigma_D\big(c(z)\,(w^{-1}n(s)y_j)\big)\big)\big\|_{\mathrm e}\, \mathrm d\nu_{Z_L}\,\mathrm d\mu_{\mathbb A} \Big) \;<\; \infty,$$
--   the sum being the `tsum` over $\kappa$ of extended non-negative reals.
--
--   Second, the function $z \mapsto \xi_L(z)\cdot \mathbf 1[\,e^R < H(c(z)x)\,]\,\mathrm{CT}(c(z)x)$ is integrable on $\Omega_L$ with respect to $\nu_{Z_L}$.
--
--   Third, writing
--   $$F^N_j = \int_{\mathbb A_L} \int \xi_L(z)\,\varphi\big((n(s)y_j)^{-1}\,\iota(\delta_0)\,\sigma_D\big(c(z)\,(n(s)y_j)\big)\big)\,\mathrm d\nu_{Z_L}\,\mathrm d\mu_{\mathbb A},$$
--   $$F^{N,w}_j = \int_{\mathbb A_L} \int \xi_L(z)\,\varphi\big((w^{-1}n(s)y_j)^{-1}\,\iota(\delta_0)\,\sigma_D\big(c(z)\,(w^{-1}n(s)y_j)\big)\big)\,\mathrm d\nu_{Z_L}\,\mathrm d\mu_{\mathbb A},$$
--   the family $j \mapsto F^N_j + F^{N,w}_j$ is summable.
--
--   Fourth, the identity
--   $$\int_{\Omega_L} \xi_L(z)\,\mathbf 1[\,e^R < H(c(z)x)\,]\,\mathrm{CT}(c(z)x)\,\mathrm d\nu_{Z_L}(z) \;=\; \mathbf 1[\,e^R < H(x)\,]\cdot \varepsilon \cdot \mu_{\mathbb A}(\mathrm{adelicBox}\,L)^{-1} \cdot \sum_{j \in \kappa}\big(F^N_j + F^{N,w}_j\big),$$
--   where the first indicator on the right is that of the set $\{y : e^R < H(y)\}$ with value $1$, the scalar $\varepsilon$ is $1/2$ if $N_{L/K}\big((\delta_0)_{00}/(\delta_0)_{11}\big) = -1$ and $1$ otherwise, the volume factor is the inverse of the real number $\mu_{\mathbb A}(\mathrm{adelicBox}\,L).\mathrm{toReal}$ viewed in $\mathbb C$, and the sum over $\kappa$ is a `tsum`.
--
--   This is the pointwise unfolding, at a single adelic point $x$ and truncation parameter $e^R$, of the constant term of the sum over one $\sigma$-twisted conjugacy class of a regular hyperbolic diagonal element $\delta_0$: the upper-triangular part of the class splits into the orbits of $\delta_0$ and of its Weyl conjugate, and the unipotent integral over the box unfolds to $\mathbb A_L$ against the normalised measure, producing the factor $\mathrm{vol}(\text{box})^{-1}$ and the factor $1/2$ in the case of norm $-1$, where the two orbits coincide. It feeds the statements that assemble the truncated hyperbolic contributions for factorisable test functions in the twisted trace formula comparison for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital.lean

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
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel in
open scoped TensorProduct.RightActions Classical in

theorem AutomorphicForm.setIntegral_mul_indicator_highSet_constantTerm_finsum_eq_indicator_mul_tsum_integral_unipotentGL2_twistedOrbital
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (Λ' : Subgroup (GL (Fin 2) L))
    (hΛ' : ∀ a : GL (Fin 2) L, a ∈ Λ' ↔ ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 0 / (a : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    {κ : Type} [Countable κ] (ra : κ → GL (Fin 2) L)
    (hrad : ∀ j, ((ra j : Matrix (Fin 2) (Fin 2) L)) 1 0 = 0 ∧ ((ra j : Matrix (Fin 2) (Fin 2) L)) 0 1 = 0)
    (hra : ∀ a : GL (Fin 2) L, ((a : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (a : Matrix (Fin 2) (Fin 2) L) 0 1 = 0) → ∃! j, (ra j)⁻¹ * a ∈ Λ')
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ)
    (x : AdelicGL2 (𝓞 L) L) (R : ℝ) :
    (∑' j, ((∫⁻ s : AdeleRing (𝓞 L) L, (∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ‖φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))))‖ₑ ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
        (∫⁻ s : AdeleRing (𝓞 L) L, (∫⁻ z, ‖((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ₑ * ‖φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))))‖ₑ ∂νZL) ∂(adelicAddHaar (𝓞 L) L)))) < ⊤ ∧
    IntegrableOn (fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)) (@AutomorphicForm.constantTerm _ (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _ (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t) (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))) (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ΩL νZL ∧
    Summable (fun j => ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)))) ∧
    ∫ z in ΩL, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
        Set.indicator (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)) (@AutomorphicForm.constantTerm _ (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _ (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν (fun t => AutomorphicForm.unipotentGL2 t) (fun y => ∑ᶠ δ ∈ {γ : GL (Fin 2) L | (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ γ ∈ I}, φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ * AutomorphicForm.sigmaAdelicAct K L D σ y))) (AutomorphicForm.centralScalar (𝓞 L) L z * x) ∂νZL =
      Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y} (fun _ => (1 : ℂ)) x *
        ((if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) * (((adelicAddHaar (𝓞 L) L (adelicBox L)).toReal⁻¹ : ℝ) : ℂ) *
          ∑' j, ((∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ ((AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)) +
          (∫ s : AdeleRing (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ * AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.adelicWeyl (𝓞 L) L)⁻¹ * AutomorphicForm.unipotentGL2 s * ((AutomorphicForm.globalPoints (𝓞 L) L (ra j))⁻¹ * x)))) ∂νZL) ∂(adelicAddHaar (𝓞 L) L)))) := by sorry
