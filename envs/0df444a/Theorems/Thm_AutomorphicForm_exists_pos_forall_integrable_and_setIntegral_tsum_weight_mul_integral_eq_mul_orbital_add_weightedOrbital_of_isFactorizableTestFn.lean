-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_integrable_and_setIntegral_tsum_weight_mul_integral_eq_mul_orbital_add_weightedOrbital_of_isFactorizableTestFn
-- name    : AutomorphicForm.exists_pos_forall_integrable_and_setIntegral_tsum_weight_mul_integral_eq_mul_orbital_add_weightedOrbital_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/8fa075d1-f761-5e8e-8221-6b184d487c12
-- title:
--   Truncated hyperbolic σ-class term as weighted twisted orbital integrals
-- statement:
--   Throughout, $K \subseteq L$ are number fields with $L/K$ Galois, and $\mathrm{GL}_2(\mathbb{A}_L)$ denotes `AdelicGL2 (𝓞 L) L`, the general linear group of degree $2$ over the adele ring of $L$, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 L) L`. Two monoid homomorphisms are used for comparison: `globalPoints (𝓞 L) L`, the map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ induced by $L \to \mathbb{A}_L$, and `centralScalar (𝓞 L) L`, the map $\mathbb{A}_L^\times \to \mathrm{GL}_2(\mathbb{A}_L)$ sending $z$ to the scalar matrix $z$.
--
--   The data and hypotheses are as follows.
--
--   *Slab bounds.* Reals $\alpha, \beta$ with $0 < \alpha$ and $\alpha < \beta$. The determinant slab is the set of $g$ with $\mathrm{ideleNorm}_L(\det g) \in [\alpha,\beta]$, where [`NumberField.TateGlobal.ideleNorm L x`](def/NumberField_TateGlobalZeta.html#L19) is the real number attached to an idele $x$ by the distributive Haar character of $\mathbb{A}_L$.
--
--   *An auxiliary set.* A set $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$, which enters as a parameter with no hypothesis attached to it.
--
--   *Central measure data.* A Haar measure $\nu_{Z L}$ on $\mathbb{A}_L^\times$ (with the measurable and Borel structures on $\mathbb{A}_L^\times$ as instance arguments) and a set $\Omega_L \subseteq \mathbb{A}_L^\times$ which, by `hΩL`, is a fundamental domain for the action of the image of $L^\times$ in $\mathbb{A}_L^\times$ with respect to $\nu_{Z L}$.
--
--   *Descent datum and generator.* An [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a monoid homomorphism $D.\mathrm{act}$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is compatible with the given Galois action on $L$ via $L \to \mathbb{A}_L$ and is continuous for each element; an element $\sigma$ of $\mathrm{Gal}(L/K)$ such that, by `hgen`, every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Here `sigmaAdelicAct K L D σ` is the automorphism of $\mathrm{GL}_2(\mathbb{A}_L)$ obtained by applying $D.\mathrm{act}\,\sigma$ entrywise, and `D.unitsAct σ` is the induced automorphism of $\mathbb{A}_L^\times$.
--
--   *Character.* A homomorphism $\xi_L$ from the full subgroup $\top \le \mathbb{A}_L^\times$ to $\mathbb{C}^\times$ such that $z \mapsto \xi_L(z) \in \mathbb{C}$ is continuous (`hξc`), $\xi_L$ is trivial on the image of $L^\times$ (`hξt`), and $\xi_L$ is $\sigma$-invariant in the sense $\xi_L(D.\mathrm{unitsAct}\,\sigma\,z) = \xi_L(z)$ for all $z$ (`hξσ`).
--
--   *Siegel and fundamental-domain data.* Reals $c, u, d_1, d_2$ with $0 < c$, a compact set $T_c \subseteq \mathrm{GL}_2(\mathbb{A}_L)$, and a set $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ subject to three conditions: `hΦ₀S`, that $\Phi_0$ is contained in the union over $y \in T_c$ of the right translates by $y$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` (the set of $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place $w$ has local height at least $c$ and squared $x$-window at most $u^2$, and whose archimedean determinant norm at every $w$ lies in $[d_1,d_2]$); `hΦ₀s`, that $\Phi_0$ lies in the determinant slab; and `hΦ₀`, that $\Phi_0$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(L)$ under `globalPoints (𝓞 L) L` with respect to the adelic Haar measure restricted to the determinant slab.
--
--   *The twisted diagonal group.* A subgroup $H \le \mathrm{GL}_2(\mathbb{A}_L)$ which is closed (`hHc`) and is characterised by `hH`: $h \in H$ if and only if the $(1,0)$ and $(0,1)$ entries of $h$ vanish and $\mathrm{sigmaAdelicAct}(h)\,h^{-1}$ lies in the centre of $\mathrm{GL}_2(\mathbb{A}_L)$; together with a measure $\mu_H$ on $H$ that is a Haar measure and right invariant. The quotient $\mathrm{GL}_2(\mathbb{A}_L)$ by the orbit relation of $H$ carries the measure [`HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH`](def/HaarQuotient.html#L28), the pushforward along the quotient map of the adelic Haar measure weighted by the associated density.
--
--   The conclusion asserts the existence of a real $\kappa > 0$, depending only on the above data, with the following property. Let $\delta_0 \in \mathrm{GL}_2(L)$ have vanishing $(1,0)$ and $(0,1)$ entries (`hδ₀u`, `hδ₀l`) and satisfy the regularity condition $N_{L/K}\bigl((\delta_0)_{00}/(\delta_0)_{11}\bigr) \neq 1$ (`hreg`, with `Algebra.norm K`). Let $I \subseteq \mathrm{GL}_2(L)$ be characterised by `hI`: $\delta \in I$ if and only if there exists $g \in \mathrm{GL}_2(L)$ with $\delta_0^{-1}\bigl(g^{-1}\,\delta\,\sigma(g)\bigr)$ central, where $\sigma(g)$ means the entrywise application of $\sigma$. Let $\Lambda \le \mathrm{GL}_2(L)$ be characterised by `hΛ`: $\gamma \in \Lambda$ if and only if $\delta_0^{-1}\bigl(\gamma\,\delta_0\,\sigma(\gamma)^{-1}\bigr)$ is central. Let $\iota$ be a countable type and $r : \iota \to \mathrm{GL}_2(L)$ a family such that, by `hr`, every $\gamma \in \mathrm{GL}_2(L)$ satisfies $(r\,i)^{-1}\gamma \in \Lambda$ for exactly one $i$, i.e. $r$ is a system of representatives for the cosets $\gamma\Lambda$. Finally let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ satisfy `IsFactorizableTestFn L φ`, i.e. $\varphi(g) = f_a(\mathrm{arch}\,g)\,f_f(\mathrm{fin}\,g)$ for some archimedean factor $f_a$ which is compactly supported and given by a $C^\infty$ function of the matrix entries in the mixed space of $L$, and some factor $f_f$ at the finite places satisfying `IsFinTestFactor`.
--
--   Write, for $y \in \mathrm{GL}_2(\mathbb{A}_L)$,
--   $$F(y) = \int_{\mathbb{A}_L^\times} \xi_L(z)\,\varphi\bigl(y^{-1}\,\delta_0\,\mathrm{sigmaAdelicAct}(z\,y)\bigr)\,d\nu_{Z L}(z),$$
--   where $\delta_0$ and $z$ stand for their images under `globalPoints` and `centralScalar`, write $\mathrm{ht} =$ [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158) (the product of the archimedean and finite heights of the two parts of $g$) and $w =$ `adelicWeyl (𝓞 L) L`, the image in $\mathrm{GL}_2(\mathbb{A}_L)$ of the Weyl element of $\mathrm{GL}_2(L)$. The conclusion has two parts.
--
--   First, both of the following functions on the $H$-orbit quotient are integrable for the quotient measure, each evaluated at a chosen representative `q.out` of the class $q$: the twisted orbital integrand $q \mapsto F(q.\mathrm{out})$, and its weighted version $q \mapsto \bigl(-\log \mathrm{ht}(q.\mathrm{out}) - \log \mathrm{ht}(w\,q.\mathrm{out})\bigr)F(q.\mathrm{out})$, the real weight being read as a complex number.
--
--   Secondly, there exists $R_1 \in \mathbb{R}$ such that for every $R \ge R_1$ the truncated class sum
--   $$x \mapsto \sum_{i}\Bigl(1 - \mathbf{1}_{\{\mathrm{ht} > e^{R}\}}\bigl((r\,i)^{-1}x\bigr) - \mathbf{1}_{\{y : \mathrm{ht}(w y) > e^{R}\}}\bigl((r\,i)^{-1}x\bigr)\Bigr)\,F\bigl((r\,i)^{-1}x\bigr)$$
--   (with $r\,i$ again meaning its image under `globalPoints`, and the indicators taking the value $1$ on the indicated sets) is integrable on $\Phi_0$ for the adelic Haar measure, and its integral over $\Phi_0$ equals
--   $$\Bigl(\kappa \cdot \epsilon\Bigr)\Bigl(2R\int F(q.\mathrm{out})\,d\bar\mu + \int \bigl(-\log \mathrm{ht}(q.\mathrm{out}) - \log \mathrm{ht}(w\,q.\mathrm{out})\bigr)F(q.\mathrm{out})\,d\bar\mu\Bigr),$$
--   where $\bar\mu$ is the quotient measure [`HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH`](def/HaarQuotient.html#L28) and $\epsilon = 1/2$ if $N_{L/K}\bigl((\delta_0)_{00}/(\delta_0)_{11}\bigr) = -1$ and $\epsilon = 1$ otherwise. The sets $I$ and the hypothesis `hI` occur as data of the statement; $\Lambda$ and $r$ enter through the coset sum on the left-hand side.
--
--   This is the evaluation of a single regular hyperbolic $\sigma$-conjugacy class on the geometric side of the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a cyclic extension $L/K$, with $\sigma$-invariant central character: the truncated class integral over the determinant slab is expressed as an explicit positive constant times $2R$ times the twisted orbital integral plus the weighted twisted orbital integral, the weight being the logarithmic height combination associated with the two truncation indicators. It is used in the theorem that sums the hyperbolic classes and subtracts the constant-term contribution, producing the hyperbolic part of the twisted trace formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_integrable_and_setIntegral_tsum_weight_mul_integral_eq_mul_orbital_add_weightedOrbital_of_isFactorizableTestFn.lean

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

theorem AutomorphicForm.exists_pos_forall_integrable_and_setIntegral_tsum_weight_mul_integral_eq_mul_orbital_add_weightedOrbital_of_isFactorizableTestFn
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
    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩) :
    ∃ κ : ℝ, 0 < κ ∧
    ∀ (δ₀ : GL (Fin 2) L) (hδ₀u : (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (hδ₀l : (δ₀ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (hreg : Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (I : Set (GL (Fin 2) L))
    (hI : ∀ δ, δ ∈ I ↔ ∃ g : GL (Fin 2) L,
      δ₀⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L))
    (Λ : Subgroup (GL (Fin 2) L))
    (hΛ : ∀ γ, γ ∈ Λ ↔
      δ₀⁻¹ * (γ * δ₀ * (Matrix.GeneralLinearGroup.map (σ : L →+* L) γ)⁻¹) ∈ Subgroup.center (GL (Fin 2) L))
    {ι : Type} [Countable ι] (r : ι → GL (Fin 2) L) (hr : ∀ γ : GL (Fin 2) L, ∃! i, (r i)⁻¹ * γ ∈ Λ)
      (φ : AdelicGL2 (𝓞 L) L → ℂ), AutomorphicForm.IsFactorizableTestFn L φ →
      (Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
          (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
       Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
          (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ∧
      ∃ R₁ : ℝ, ∀ R : ℝ, R₁ ≤ R →
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
        ((κ : ℂ) * (if Algebra.norm K ((δ₀ : Matrix (Fin 2) (Fin 2) L) 0 0 / (δ₀ : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
          ((R : ℂ) * 2 * ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) +
            ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) := by sorry
