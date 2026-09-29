-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_tsum_bracket_mul_twistedOrbital_and_setIntegral_eq_mul_integral_setIntegral_indicator_bracket_mul
-- name    : AutomorphicForm.integrableOn_tsum_bracket_mul_twistedOrbital_and_setIntegral_eq_mul_integral_setIntegral_indicator_bracket_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/274d8ee3-d17f-578e-9acb-ae01382c4bab
-- title:
--   Unfolding one σ-twisted hyperbolic class over the centraliser quotient
-- statement:
--   Throughout, $K \subseteq L$ are number fields with $L/K$ Galois, and $\mathrm{GL}_2(\mathbb{A}_L)$ denotes `AdelicGL2 (𝓞 L) L`, the general linear group of degree $2$ over the adele ring of $L$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L`. Write $\iota$ for [`AutomorphicForm.globalPoints (𝓞 L) L`](def/AutomorphicForm_AdelicLsXi.html#L15), the entrywise map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ induced by $L \to \mathbb{A}_L$; write $z \mapsto \langle z\rangle$ for [`AutomorphicForm.centralScalar (𝓞 L) L`](def/AutomorphicForm_AdelicLsXi.html#L18), the embedding of $\mathbb{A}_L^\times$ as scalar matrices; write $w$ for [`AutomorphicForm.adelicWeyl (𝓞 L) L`](def/AutomorphicForm_WeylIntertwining.html#L35), the image under $\iota$ of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$; write $\mathrm{ht}_L$ for [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158), the product of the archimedean and the finite height of the corresponding components; and write $\|\cdot\|_L$ for [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19), the value of the distributive Haar character of $\mathbb{A}_L$ at an idele, regarded as a real number.
--
--   **Frame data.** Real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a subset $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$, to which no condition is attached; a measurable and Borel structure on $\mathbb{A}_L^\times$, a Haar measure $\nu_{Z_L}$ on $\mathbb{A}_L^\times$ and a set $\Omega_L \subseteq \mathbb{A}_L^\times$ which by $h\Omega_L$ is a fundamental domain for the range of $L^\times \to \mathbb{A}_L^\times$ acting on $\mathbb{A}_L^\times$ with respect to $\nu_{Z_L}$. A datum $D$ of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a homomorphism $\tau \mapsto D.\mathrm{act}\,\tau$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is compatible with the action on $L$ through $L \to \mathbb{A}_L$ and continuous in each $\tau$; an element $\sigma \in \mathrm{Gal}(L/K)$ with $h_{\mathrm{gen}}$: every $\tau$ lies in the subgroup of integral powers of $\sigma$. Write $\sigma_D$ for [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14), the entrywise application of $D.\mathrm{act}\,\sigma$ to matrices, and $D.\mathrm{unitsAct}\,\sigma$ for the induced automorphism of $\mathbb{A}_L^\times$.
--
--   **Character hypotheses.** A homomorphism $\xi_L$ from the full subgroup $\top \le \mathbb{A}_L^\times$ to $\mathbb{C}^\times$ such that $z \mapsto \xi_L(z) \in \mathbb{C}$ is continuous ($h\xi c$), $\xi_L$ is trivial on the image of $L^\times$ ($h\xi t$), and $\xi_L$ is invariant under $D.\mathrm{unitsAct}\,\sigma$ ($h\xi\sigma$).
--
--   **Fundamental-domain hypotheses for $\mathrm{GL}_2(L)$.** Real numbers $c,u,d_1,d_2$ with $0<c$; a compact set $T_c \subseteq \mathrm{GL}_2(\mathbb{A}_L)$; a set $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ such that ($h\Phi_0 S$) $\Phi_0$ is contained in the union over $y \in T_c$ of the right translates by $y$ of `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂`, the set of $g$ whose finite component lies in the finite integral part `finiteIntegralGL2 (𝓞 L) L`, whose archimedean component at every infinite place has local height at least $c$ and $x$-window square at most $u^2$, and whose archimedean determinant norm at every infinite place lies in $[d_1,d_2]$; ($h\Phi_0 s$) $\Phi_0$ is contained in the determinant slab $S := \{g : \|\det g\|_L \in [\alpha,\beta]\}$; and ($h\Phi_0$) $\Phi_0$ is a fundamental domain for the range of $\iota$ acting on $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to the adelic Haar measure restricted to $S$.
--
--   **The twisted centraliser group.** A subgroup $H \le \mathrm{GL}_2(\mathbb{A}_L)$ which is closed ($hHc$) and satisfies ($hH$): $h \in H$ if and only if the $(1,0)$ and $(0,1)$ entries of $h$ vanish and $\sigma_D(h)\,h^{-1}$ lies in the centre of $\mathrm{GL}_2(\mathbb{A}_L)$; together with a Haar measure $\mu_H$ on $H$ that is also right invariant.
--
--   **The class data.** An element $\delta_0 \in \mathrm{GL}_2(L)$ which is diagonal ($h\delta_0 u$, $h\delta_0 l$: its $(1,0)$ and $(0,1)$ entries vanish) and regular in the sense ($h_{\mathrm{reg}}$) that $N_{L/K}\bigl((\delta_0)_{00}/(\delta_0)_{11}\bigr) \neq 1$; a set $I \subseteq \mathrm{GL}_2(L)$ with ($hI$) $\delta \in I$ if and only if there is $g \in \mathrm{GL}_2(L)$ with $\delta_0^{-1}\bigl(g^{-1}\,\delta\,\sigma(g)\bigr)$ central, $\sigma(g)$ meaning the entrywise application of $\sigma$; a subgroup $\Lambda \le \mathrm{GL}_2(L)$ with ($h\Lambda$) $\gamma \in \Lambda$ if and only if $\delta_0^{-1}\bigl(\gamma\,\delta_0\,\sigma(\gamma)^{-1}\bigr)$ is central; a countable type $\iota$-index set with a family $r : \iota \to \mathrm{GL}_2(L)$ which by ($hr$) is a system of representatives for the left cosets of $\Lambda$: for every $\gamma$ there is exactly one index $i$ with $(r\,i)^{-1}\gamma \in \Lambda$.
--
--   **The inner fundamental domain.** A subgroup $\Lambda_0 \le \mathrm{GL}_2(L)$ with ($h\Lambda_0$) $\gamma \in \Lambda_0$ if and only if $\gamma$ is diagonal and $\gamma_{00}/\gamma_{11}$ lies in the image of $K \to L$; and a set $\Omega \subseteq H$ which by ($h\Omega$) is a fundamental domain, with respect to $\mu_H$, for the image $\iota(\Lambda_0)$ viewed as a subgroup of $H$.
--
--   **Test function and truncation.** A continuous $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ with compact support, and a real number $R$. Put
--   $$b(x) \;=\; 1 - \mathbf 1[\exp R < \mathrm{ht}_L(x)] - \mathbf 1[\exp R < \mathrm{ht}_L(w\,x)], \qquad F(y) \;=\; \int_{\mathbb{A}_L^\times} \xi_L(z)\,\varphi\bigl(y^{-1}\,\iota(\delta_0)\,\sigma_D(\langle z\rangle\,y)\bigr)\, d\nu_{Z_L}(z),$$
--   where the indicators are the complex-valued indicator functions of the two stated subsets of $\mathrm{GL}_2(\mathbb{A}_L)$.
--
--   **Convergence hypothesis ($h_{\mathrm{fin}}$).** With [`HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH`](def/HaarQuotient.html#L28) the measure on the orbit space $H\backslash \mathrm{GL}_2(\mathbb{A}_L)$ obtained by pushing forward the adelic Haar measure, weighted by the density attached to $H$ and $\mu_H$, along the quotient map, and $q.\mathrm{out}$ a chosen representative of the class $q$, the iterated lower integral
--   $$\int_{H\backslash \mathrm{GL}_2(\mathbb{A}_L)} \Bigl( \int^-_{\Omega} \bigl\| \mathbf 1_S(h\,q.\mathrm{out})\, b(h\,q.\mathrm{out}) \bigr\|_{e} \, d\mu_H(h) \Bigr) \cdot \bigl\| F(q.\mathrm{out}) \bigr\|_{e} \, dq$$
--   is finite, the indicator $\mathbf 1_S$ being complex valued.
--
--   **Conclusion.** Three assertions hold simultaneously.
--
--   First, the function
--   $$x \longmapsto \sum_{i} b\bigl(\iota(r\,i)^{-1}x\bigr)\, F\bigl(\iota(r\,i)^{-1}x\bigr)$$
--   is integrable on $\Phi_0$ with respect to the adelic Haar measure; here no slab indicator occurs in the summand.
--
--   Second, the function
--   $$q \longmapsto \Bigl( \int_{\Omega} \mathbf 1_S(h\,q.\mathrm{out})\, b(h\,q.\mathrm{out}) \, d\mu_H(h) \Bigr) \cdot F(q.\mathrm{out})$$
--   on $H\backslash \mathrm{GL}_2(\mathbb{A}_L)$ is integrable with respect to the quotient measure.
--
--   Third, the two integrals agree up to an explicit constant:
--   $$\int_{\Phi_0} \sum_{i} b\bigl(\iota(r\,i)^{-1}x\bigr)\,F\bigl(\iota(r\,i)^{-1}x\bigr)\, dx \;=\; \varepsilon \cdot \int_{H\backslash \mathrm{GL}_2(\mathbb{A}_L)} \Bigl( \int_{\Omega} \mathbf 1_S(h\,q.\mathrm{out})\, b(h\,q.\mathrm{out})\, d\mu_H(h) \Bigr) F(q.\mathrm{out})\, dq,$$
--   where $\varepsilon = 1/2$ if $N_{L/K}\bigl((\delta_0)_{00}/(\delta_0)_{11}\bigr) = -1$ and $\varepsilon = 1$ otherwise.
--
--   This is the unfolding step for a single regular $\sigma$-twisted hyperbolic class on the geometric side of the twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$: the truncated class sum over a Siegel-type fundamental domain inside the determinant slab is rewritten as an integral over the twisted centraliser quotient, with the factor $1/2$ appearing exactly when the relevant norm equals $-1$. It is an identity between integrals for a fixed test function and a fixed class, carrying no estimate, and it feeds the class-evaluation theorems [`AutomorphicForm.exists_pos_forall_integrable_and_setIntegral_tsum_weight_mul_integral_eq_mul_orbital_add_weightedOrbital_of_isFactorizableTestFn`](thm.html#AutomorphicForm.exists_pos_forall_integrable_and_setIntegral_tsum_weight_mul_integral_eq_mul_orbital_add_weightedOrbital_of_isFactorizableTestFn) and [`AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn`](thm.html#AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_tsum_bracket_mul_twistedOrbital_and_setIntegral_eq_mul_integral_setIntegral_indicator_bracket_mul.lean

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

open scoped TensorProduct.RightActions in
open scoped Classical in

theorem AutomorphicForm.integrableOn_tsum_bracket_mul_twistedOrbital_and_setIntegral_eq_mul_integral_setIntegral_indicator_bracket_mul
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
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
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))

    (H : Subgroup (AdelicGL2 (𝓞 L) L)) (hHc : IsClosed (H : Set (AdelicGL2 (𝓞 L) L)))
    (hH : ∀ h : AdelicGL2 (𝓞 L) L, h ∈ H ↔
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 0 = 0 ∧
       (h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = 0 ∧
       AutomorphicForm.sigmaAdelicAct K L D σ h * h⁻¹ ∈ Subgroup.center (AdelicGL2 (𝓞 L) L)))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩)
    (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
    (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    (Ω : Set H) (hΩ : IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφc : Continuous φ) (hφs : HasCompactSupport φ) (R : ℝ)
    (hfin : ∫⁻ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), (∫⁻ h in Ω, ‖Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L)) *
              ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L))
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L)))‖ₑ ∂μH) * ‖(∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)‖ₑ ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) < ⊤) :
    IntegrableOn (fun x : AdelicGL2 (𝓞 L) L => ∑' i,
      (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
      (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
      - Set.indicator {y : AdelicGL2 (𝓞 L) L |
      Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
      (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
      ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
      φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
      AutomorphicForm.sigmaAdelicAct K L D σ
      (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL)
      Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => (∫ h in Ω, Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L)) *
              ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L))
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L))) ∂μH) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)) (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
    ∫ x in Φ₀, ∑' i,
        (1 - Set.indicator {y : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)
           - Set.indicator {y : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y)}
              (fun _ => (1 : ℂ)) ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)) *
        ∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
          φ (((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
            AutomorphicForm.sigmaAdelicAct K L D σ
              (AutomorphicForm.centralScalar (𝓞 L) L z * ((AutomorphicForm.globalPoints (𝓞 L) L (r i))⁻¹ * x))) ∂νZL
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L) =
      (if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
          then (1 / 2 : ℂ) else 1) *
        ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), (∫ h in Ω, Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L)) *
              ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L))
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * (q.out : AdelicGL2 (𝓞 L) L))) ∂μH) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL) ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) := by sorry
