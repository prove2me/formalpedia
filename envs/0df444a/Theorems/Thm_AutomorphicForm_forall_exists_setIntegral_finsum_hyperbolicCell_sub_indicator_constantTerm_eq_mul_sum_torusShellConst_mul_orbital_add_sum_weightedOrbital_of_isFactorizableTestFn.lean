-- Prove2me | Theorems.Thm_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn
-- name    : AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/456eb73d-ff72-584f-8915-f33d9abc6dd3
-- title:
--   Pinned fine expansion of the truncated twisted hyperbolic term
-- statement:
--   Throughout, $K \subseteq L$ are number fields with $L/K$ Galois, $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, and `AdelicGL2 (𝓞 L) L` $= \mathrm{GL}_2(\mathbb{A}_L)$; `globalPoints` is the entrywise map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$ induced by $L \to \mathbb{A}_L$, `centralScalar` sends an idele unit $z$ to the scalar matrix $z I$, and `adelicWeyl` is the global point $w = \begin{pmatrix}0&1\\1&0\end{pmatrix}$. The height $H$ is [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158), the product of the archimedean height $\prod_v \mathrm{localHeight}(g_v)^{\mathrm{mult}(v)}$ of the archimedean component with the finite height $\prod_v^{\mathrm{f}} \mathrm{finLocalHeight}(g_v)$; [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19) is the idele norm given by the distributive Haar character.
--
--   The data are grouped as follows.
--
--   *Slab and central data.* Reals $\alpha, \beta$ with $0 < \alpha$ and $\alpha < \beta$; a set $\Phi_L \subseteq \mathrm{GL}_2(\mathbb{A}_L)$; a Haar measure $\nu_{Z L}$ on $\mathbb{A}_L^\times$ and a set $\Omega_L \subseteq \mathbb{A}_L^\times$ which (`hΩL`) is a fundamental domain for the range of $L^\times \to \mathbb{A}_L^\times$ acting on $\mathbb{A}_L^\times$ with respect to $\nu_{ZL}$.
--
--   *Descent and Galois data.* An [`M4aHerbrand.IdeleGaloisDescent`](def/M4aHerbrand_IdeleClassVocab.html#L28) $D$ for $\mathcal{O}_L, K, L$, i.e. a homomorphism $\mathrm{Gal}(L/K) \to \mathrm{Aut}_{\mathrm{ring}}(\mathbb{A}_L)$ compatible with the $L$-points and continuous in each element; an element $\sigma \in \mathrm{Gal}(L/K)$ with (`hgen`) every $\tau$ lying in the subgroup of integer powers of $\sigma$. The map `sigmaAdelicAct K L D σ` is the entrywise application of $D.\mathrm{act}\,\sigma$ to $\mathrm{GL}_2(\mathbb{A}_L)$.
--
--   *Character data.* A homomorphism $\xi_L$ from the top subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$, whose associated function $z \mapsto \xi_L(z)$ is continuous (`hξc`), which is trivial on the principal ideles (`hξt`), and which is $\sigma$-invariant in the sense that $\xi_L(D.\mathrm{unitsAct}\,\sigma\,z) = \xi_L(z)$ for all $z$ (`hξσ`).
--
--   *Siegel and fundamental-domain data for the quotient.* Reals $c, u, d_1, d_2$ with $0 < c$, a compact set $T_c \subseteq \mathrm{GL}_2(\mathbb{A}_L)$, and a set $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_L)$ such that (`hΦ₀S`) $\Phi_0$ is contained in the union over $y \in T_c$ of the right translates by $y$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` — the $g$ whose finite part lies in $\mathrm{GL}_2$ of the integral finite adeles, with $c \le \mathrm{localHeight}$ at every infinite place, $\mathrm{xWindowSq} \le u^2$ at every infinite place, and archimedean determinant norm in $[d_1, d_2]$ at every infinite place — such that (`hΦ₀s`) the idele norm of $\det g$ lies in $[\alpha, \beta]$ for $g \in \Phi_0$, and such that (`hΦ₀`) $\Phi_0$ is a fundamental domain for the range of `globalPoints` with respect to the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to the determinant slab $\{g : \lVert \det g\rVert \in [\alpha,\beta]\}$.
--
--   *Twisted torus.* A subgroup $H \le \mathrm{GL}_2(\mathbb{A}_L)$ which is closed (`hHc`) and is characterised (`hH`) by: $h \in H$ iff the $(1,0)$ and $(0,1)$ entries of $h$ vanish and $\sigma(h)h^{-1}$ is central in $\mathrm{GL}_2(\mathbb{A}_L)$, where $\sigma(h) =$ `sigmaAdelicAct K L D σ h`; together with a right-invariant Haar measure $\mu_H$ on $H$.
--
--   *Lattice and shell-constant data.* A subgroup $\Lambda_0 \le \mathrm{GL}_2(L)$ characterised (`hΛ₀`) by: $\gamma \in \Lambda_0$ iff $\gamma_{10} = \gamma_{01} = 0$ and $\gamma_{00}/\gamma_{11}$ lies in the image of $K \to L$; a real $\kappa_0 > 0$; a set $\Omega \subseteq H$ which (`hΩ`) is a fundamental domain for the image of $\Lambda_0$ under `globalPoints`, viewed as a subgroup of $H$, with respect to $\mu_H$; the hypothesis `hκ₀`, asserting that for all $y \in \mathrm{GL}_2(\mathbb{A}_L)$ and all $R \in \mathbb{R}$,
--   $$\int^{-}_{h \in \Omega} \big\lVert \mathbf{1}_{\{\lVert\det\rVert \in [\alpha,\beta]\}}(hy)\,\big(1 - \mathbf{1}_{\{H > e^R\}}(hy) - \mathbf{1}_{\{H(w\,\cdot) > e^R\}}(hy)\big)\big\rVert_{e}\, d\mu_H = \kappa_0\,\big|\,2R - \log H(y) - \log H(wy)\,\big|$$
--   (the right-hand side as an extended nonnegative real via `ENNReal.ofReal`, the indicators being complex-valued indicators of value $1$); and the hypothesis `hκ₀'`, asserting that for all $y$ and $R$, if $H(y)\,H(wy) \le e^{2R}$ then the same integrand is integrable on $\Omega$ for $\mu_H$ and its integral equals the complex number $\kappa_0\big(2R - \log H(y) - \log H(wy)\big)$.
--
--   *Class representatives.* A set $\Delta \subseteq \mathrm{GL}_2(L)$ such that (`hΔd`) every $t \in \Delta$ has $t_{10} = t_{01} = 0$ and $\mathrm{N}_{K}(t_{00}/t_{11}) \ne 1$ (the relative algebra norm `Algebra.norm K`); such that (`hΔdisj`) for distinct $t, t' \in \Delta$ the sets $\{\delta : \exists g,\ t^{-1} g^{-1}\delta\,\sigma(g) \text{ is central}\}$ and the corresponding set for $t'$ are disjoint, $\sigma(g)$ denoting the entrywise application of $\sigma$ to $g \in \mathrm{GL}_2(L)$; and such that (`hΔcov`) the set
--   $$\mathcal{C} = \{\delta \in \mathrm{GL}_2(L) : \exists\, \gamma \in \mathrm{GL}_2(K),\ \gamma \in \mathrm{hyperbolicCell}(K)\ \text{and}\ \mathrm{normClassMap}_{hgen}([\delta]_\sigma) = [\gamma]\}$$
--   is contained in $\bigcup_{t \in \Delta}\{\delta : \exists g,\ t^{-1} g^{-1}\delta\,\sigma(g) \text{ is central}\}$. Here `hyperbolicCell K` consists of the $\gamma$ whose characteristic polynomial factors as $(X - a)(X - b)$ with $a \ne b$ in $K$, $[\delta]_\sigma$ is the class of $\delta$ for $\sigma$-twisted conjugacy, and $\mathrm{normClassMap}_{hgen}$ is the induced map from $\sigma$-twisted conjugacy classes in $\mathrm{GL}_2(L)$ to conjugacy classes in $\mathrm{GL}_2(K)$.
--
--   The conclusion is the following assertion for every $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ satisfying [`AutomorphicForm.IsFactorizableTestFn L φ`](def/AutomorphicForm_FactorizableTestFn.html#L38), i.e. $\varphi(g) = f_\infty(g_\infty) f_{\mathrm{fin}}(g_{\mathrm{fin}})$ where $f_\infty$ is compactly supported and given by a $C^\infty$ function of the mixed-space matrix entries, and $f_{\mathrm{fin}}$ is locally constant with compact support. There exists a finite set $\Delta_\varphi$ of elements of $\mathrm{GL}_2(L)$ with:
--
--   (i) $\Delta_\varphi \subseteq \Delta$;
--
--   (ii) for every $t \in \Delta$ with $t \notin \Delta_\varphi$ and every $y \in \mathrm{GL}_2(\mathbb{A}_L)$, the twisted orbital integral vanishes:
--   $$\int_{\mathbb{A}_L^\times} \xi_L(z)\,\varphi\big(y^{-1}\,t\,\sigma(zI \cdot y)\big)\, d\nu_{ZL}(z) = 0,$$
--   where $t$ is read in $\mathrm{GL}_2(\mathbb{A}_L)$ via `globalPoints`;
--
--   (iii) for every $t \in \Delta_\varphi$, both of the following functions on the orbit quotient $\mathrm{orbitRel.Quotient}\,H\,\mathrm{GL}_2(\mathbb{A}_L)$ are integrable for the quotient measure [`HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH`](def/HaarQuotient.html#L28) (the push-forward of the adelic Haar measure weighted by the density [`HaarQuotient.density H μH`](def/HaarQuotient.html#L25)), evaluated on a chosen representative $q.\mathrm{out}$ of each orbit: the orbital integral
--   $$q \mapsto \int_{\mathbb{A}_L^\times} \xi_L(z)\,\varphi\big(q.\mathrm{out}^{-1}\,t\,\sigma(zI \cdot q.\mathrm{out})\big)\, d\nu_{ZL}(z),$$
--   and its height-weighted companion, obtained by multiplying the same integral by the real scalar $-\log H(q.\mathrm{out}) - \log H(w\,q.\mathrm{out})$;
--
--   (iv) there exists $R_0 \in \mathbb{R}$ such that for every $R \ge R_0$ three statements hold. Write, for $x \in \mathrm{GL}_2(\mathbb{A}_L)$ and $z \in \mathbb{A}_L^\times$,
--   $$F_{R}(x,z) = \xi_L(z)\Big(\sum^{\mathrm{f}}_{\delta \in \mathcal{C}} \varphi\big(x^{-1}\,\delta\,\sigma(zI\cdot x)\big) \;-\; \mathbf{1}_{\{g\,:\,H(g) > e^{R}\}}(zI \cdot x)\cdot \mathcal{E}(x)(zI\cdot x)\Big),$$
--   where $\sum^{\mathrm{f}}$ is the finite-support sum over $\mathcal{C}$, the indicator is that of [`AutomorphicForm.highSet`](def/AutomorphicForm_TruncationOperator.html#L36) for the height $H$ and threshold $e^R$, and $\mathcal{E}(x)$ is the constant term [`AutomorphicForm.constantTerm`](def/AutomorphicForm_ConstantTerm.html#L47) formed with the measurable space and measure taken from the `CarrierPins` record `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)` — namely the Borel $\sigma$-algebra `adeleBorel` on $\mathbb{A}_L$ and the additive adelic Haar measure conditioned on the adelic box $\mathrm{adelicBox}(L)$ — with the unipotent family $t \mapsto \begin{pmatrix}1&t\\0&1\end{pmatrix}$ and with the function
--   $$y \mapsto \sum^{\mathrm{f}}_{\delta \in \mathcal{J}} \varphi\big(x^{-1}\,\delta\,\sigma(y)\big),\qquad \mathcal{J} = \{\gamma \in \mathrm{GL}_2(L) : \gamma_{10} = 0,\ \mathrm{N}_K(\gamma_{00}/\gamma_{11}) \ne 1\},$$
--   so that $\mathcal{E}(x)(g) = \int_{\mathbb{A}_L} \sum^{\mathrm{f}}_{\delta \in \mathcal{J}} \varphi\big(x^{-1}\delta\,\sigma(u(s)g)\big)\, d\nu(s)$ for the conditioned measure $\nu$. The three statements are:
--
--   (iv.a) for every $x$, the function $z \mapsto F_R(x,z)$ is integrable on $\Omega_L$ for $\nu_{ZL}$;
--
--   (iv.b) the function $x \mapsto \int_{\Omega_L} F_R(x,z)\, d\nu_{ZL}(z)$ is integrable on $\Phi_0$ for the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$;
--
--   (iv.c) the resulting double integral is an affine function of $R$ with coefficients given by the orbital integrals of (iii):
--   $$\int_{\Phi_0}\!\!\int_{\Omega_L} F_R(x,z)\, d\nu_{ZL}(z)\, dg(x) \;=\; R\sum_{t \in \Delta_\varphi} 2\,a_t\, O_t(\varphi) \;+\; \sum_{t \in \Delta_\varphi} a_t\, WO_t(\varphi),$$
--   where $a_t = \kappa_0 \cdot \tfrac12$ if $\mathrm{N}_K(t_{00}/t_{11}) = -1$ and $a_t = \kappa_0$ otherwise, $O_t(\varphi)$ is the integral over the orbit quotient, against [`HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH`](def/HaarQuotient.html#L28), of the orbital integral $q \mapsto \int \xi_L(z)\varphi(q.\mathrm{out}^{-1} t\,\sigma(zI\cdot q.\mathrm{out}))\, d\nu_{ZL}$, and $WO_t(\varphi)$ is the integral over the same quotient of the height-weighted orbital integral, the weight being $-\log H(q.\mathrm{out}) - \log H(w\,q.\mathrm{out})$.
--
--   This is the fine expansion of the truncated $\xi_L$-folded $\sigma$-twisted hyperbolic term of the kernel of a factorisable test function on $\mathrm{GL}_2(\mathbb{A}_L)$, in the shape slope$\,\cdot R\,+\,$intercept, with all class constants expressed through the single torus-shell constant $\kappa_0$ and the sign of $\mathrm{N}_{L/K}(t_{00}/t_{11})$. It is used by the two statements that extract the affine shape of the truncated twisted hyperbolic term and identify its slope and intercept as sums of (weighted) twisted orbital integrals over $H \backslash \mathrm{GL}_2(\mathbb{A}_L)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn.lean

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

open Classical in
open scoped TensorProduct.RightActions in

theorem AutomorphicForm.forall_exists_setIntegral_finsum_hyperbolicCell_sub_indicator_constantTerm_eq_mul_sum_torusShellConst_mul_orbital_add_sum_weightedOrbital_of_isFactorizableTestFn
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

    (Λ₀ : Subgroup (GL (Fin 2) L))
    (hΛ₀ : ∀ γ : GL (Fin 2) L, γ ∈ Λ₀ ↔ (γ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (γ : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) L) 0 0 / (γ : Matrix (Fin 2) (Fin 2) L) 1 1 ∈ Set.range (algebraMap K L))
    (κ₀ : ℝ) (hκ₀pos : 0 < κ₀) (Ω : Set H)
    (hΩ : IsFundamentalDomain ((Λ₀.map (AutomorphicForm.globalPoints (𝓞 L) L)).subgroupOf H) Ω μH)
    (hκ₀ : ∀ (y : AdelicGL2 (𝓞 L) L) (R : ℝ),
      ∫⁻ h in Ω, ‖Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
            (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
          ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
             - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                  Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
                (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))‖ₑ ∂μH =
        ENNReal.ofReal (κ₀ * |2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
          - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))|))

    (hκ₀' : ∀ (y : AdelicGL2 (𝓞 L) L) (R : ℝ),
        (NumberField.AdelicHeight.adelicHeight L y *
            NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y) ≤ Real.exp (2 * R) →
          IntegrableOn (fun h : H => Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y))) Ω μH ∧
          ∫ h in Ω, Set.indicator {g : AdelicGL2 (𝓞 L) L | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y) *
            ((1 : ℂ) - Set.indicator {y' : AdelicGL2 (𝓞 L) L | Real.exp R < NumberField.AdelicHeight.adelicHeight L y'}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)
           - Set.indicator {y' : AdelicGL2 (𝓞 L) L |
                Real.exp R < NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y')}
              (fun _ => (1 : ℂ)) ((h : AdelicGL2 (𝓞 L) L) * y)) ∂μH =
            ((κ₀ * (2 * R - Real.log (NumberField.AdelicHeight.adelicHeight L y)
              - Real.log (NumberField.AdelicHeight.adelicHeight L (AutomorphicForm.adelicWeyl (𝓞 L) L * y))) : ℝ) : ℂ)))

    (Δ : Set (GL (Fin 2) L))
    (hΔd : ∀ t ∈ Δ, (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧ (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0 ∧
      Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 1)
    (hΔdisj : ∀ t ∈ Δ, ∀ t' ∈ Δ, t ≠ t' →
      Disjoint {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)}
        {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t'⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)})
    (hΔcov : {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K, γ ∈ AutomorphicForm.hyperbolicCell K ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ} ⊆
      ⋃ t ∈ Δ, {δ : GL (Fin 2) L | ∃ g : GL (Fin 2) L,
          t⁻¹ * (g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g) ∈ Subgroup.center (GL (Fin 2) L)})

    (hξσ : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ξL ⟨D.unitsAct σ z, Subgroup.mem_top _⟩ = ξL ⟨z, Subgroup.mem_top z⟩) :
    ∀ φ : AdelicGL2 (𝓞 L) L → ℂ, AutomorphicForm.IsFactorizableTestFn L φ →
      ∃ Δφ : Finset (GL (Fin 2) L), (↑Δφ ⊆ Δ) ∧
        (∀ t ∈ Δ, t ∉ Δφ → ∀ y : AdelicGL2 (𝓞 L) L, (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ ((y)⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * (y))) ∂νZL) = 0) ∧
        (∀ t ∈ Δφ, Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) => (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
            (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) ∧
          Integrable (fun q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L) =>
            ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
              - Real.log (NumberField.AdelicHeight.adelicHeight L
                  (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL))
            (HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH)) ∧
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
        (R : ℂ) * ∑ t ∈ Δφ, 2 * ((κ₀ : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L), (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) +
        ∑ t ∈ Δφ, ((κ₀ : ℂ) * (if Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 0 0 / (t : Matrix (Fin 2) (Fin 2) L) 1 1) = -1
              then (1 / 2 : ℂ) else 1)) *
            ∫ q : MulAction.orbitRel.Quotient H (AdelicGL2 (𝓞 L) L),
              ((-Real.log (NumberField.AdelicHeight.adelicHeight L (q.out : AdelicGL2 (𝓞 L) L))
                - Real.log (NumberField.AdelicHeight.adelicHeight L
                    (AutomorphicForm.adelicWeyl (𝓞 L) L * (q.out : AdelicGL2 (𝓞 L) L))) : ℝ) : ℂ) * (∫ z, ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) *
              φ (((q.out : AdelicGL2 (𝓞 L) L))⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
                AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * ((q.out : AdelicGL2 (𝓞 L) L)))) ∂νZL)
              ∂(HaarQuotient.measure (adelicGLHaar (Fin 2) (𝓞 L) L) H μH) := by sorry
