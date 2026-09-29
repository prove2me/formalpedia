-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_torus_peel_ode_growth_and_separation_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_smul
-- name    : AutomorphicForm.whittakerCoefficient_torus_peel_ode_growth_and_separation_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/6d78425b-5f1d-53ec-910c-47a07d3ee6da
-- title:
--   Archimedean Whittaker coefficient: covariance, ODE, growth, separation
-- statement:
--   Work over $\mathbb{Q}$ with the carrier pins `productionPinsOf ℚ D U gen (adelicBox ℚ)` attached to a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, a level system $U$ on ideals of $\mathbb{Z}$ and Hecke generators `gen`, the unipotent variable being integrated against adelic Haar measure conditioned on the adelic box. Let $\psi$ be an additive character of $\mathbb{A}_\mathbb{Q}$ that is trivial on principal adeles, continuous and nontrivial, let $w$ be a real infinite place, and assume $\psi$ has real component $x \mapsto e^{2\pi i x}$ at $w$ in the sense that $\psi(x,0) = \exp(2\pi i\, \iota_w(x_w))$ whenever the infinite adele $x$ vanishes at all places other than $w$. Let $\xi$ be a character of the full idele unit group, $N$ an ideal, $S$ a finite set of finite places, $\Phi$ a Hecke eigensystem with complex coefficients, and let $\varphi$ satisfy `IsIsotypicCuspFormAt`: $\varphi$ is a smooth cuspidal automorphic function with central character $\xi$, continuous, right invariant under $U(N)$, a Hecke coset eigenfunction with eigenvalue $\Phi.a(v)$ for $v \notin S$, and of central eigenvalue $(\mathrm{cNorm}\,v)^{-1}\Phi.b(v)$ at the determinants of the generators for $v \notin S$. Assume further: $\varphi = \varphi * \alpha$ for some factorizable test function $\alpha$; $\varphi$ is archimedean-smooth at $w$; $\Omega_w\varphi = (\tfrac14 - \nu^2)\varphi$ for the Casimir operator at $w$ and some $\nu \in \mathbb{C}$; $\varphi$ transforms by the weight-$k$ character `archWeightCharAt hw k` of the row-isometry subgroup at $w$ for some $k \in \mathbb{Z}$; the archimedean component of $\xi$ at $w$ is $x \mapsto \|x\|^{\,\mathrm{mult}(w)\,u_c}(\iota_w(x)/\|x\|)^{a_c}$ for some $u_c \in \mathbb{C}$, $a_c \in \mathbb{Z}$; $W$ is the Whittaker coefficient of $\varphi$ at $\alpha = 1$, that is $W(g) = \int \varphi(n(x)g)\,\psi(-x)\,dx$; and $W$ has moderate growth along the archimedean torus: for each $t$ with trivial archimedean component there are $C, M$ with $\|W(\mathrm{diag}(a,1)t)\| \le C\,\|a\|_{\mathbb{A}}^{M}$ for all ideles $a$ with trivial finite component. The conclusion is a nine-fold conjunction. First, $W(n(X)g) = \psi(X)W(g)$ for every adele $X$ and every $g$, and $W(n(x)_w g) = e^{2\pi i x}W(g)$ for real $x$. Second and third, centre peeling: for $y > 0$, with $a(y) = \mathrm{diag}(e^{(\log y)/2}, e^{-(\log y)/2})$ placed at $w$, one has $W(a(y)g) = (\sqrt{y}^{\,-1})^{u_c}\,W(\mathrm{diag}(y,1)_w g)$, and likewise $W(\mathrm{J}\,a(y)g) = (\sqrt{y}^{\,-1})^{u_c}\,W(\mathrm{diag}(-y,1)_w g)$ for the negative-determinant reflection $\mathrm{J} =$ `UpperHalfPlane.J`. Fourth, for every $g$ with trivial archimedean component, both $y \mapsto W(a(y)g)$ and $y \mapsto W(\mathrm{J}a(y)g)$ are differentiable on $(0,\infty)$ with differentiable derivative there, and satisfy the Whittaker equation $y^2 f''(y) + (\tfrac14 - \nu^2 + 2\pi k y - 4\pi^2 y^2)f(y) = 0$ on $(0,\infty)$, with $k$ replaced by $-k$ on the $\mathrm{J}$ sheet. Fifth and sixth, on each of the two sheets and for each $g$ with trivial archimedean component there are $C', N'$ with $\|W(a(z)g)\| \le C' z^{N'}$ for all $z \ge 1$. Seventh, if $W$ is not identically zero then $W(\mathrm{diag}(r,1)_w t) \neq 0$ for some real $r \neq 0$ and some $t$ with trivial archimedean component. Eighth, separation of variables: if $t_0$ has trivial archimedean component and $W(\mathrm{diag}(y_0,1)_w t_0) \neq 0$ for some $y_0 > 0$, then for every $h$ with trivial archimedean component and every $y > 0$, $W(\mathrm{diag}(y,1)_w h)$ equals $W(\mathrm{diag}(y_0,1)_w h)/W(\mathrm{diag}(y_0,1)_w t_0)$ times $W(\mathrm{diag}(y,1)_w t_0)$. Ninth, if a function $F_{\mathrm{ref}} : \mathbb{C} \to \mathbb{C}$ and a function $\mathrm{cst}$ satisfy $W(\mathrm{diag}(r,1)_w h) = \mathrm{cst}(h)F_{\mathrm{ref}}(r)$ for all $h$ with trivial archimedean component and all real $r \neq 0$, then for every $\rho \neq 0$ there is a function $C$ of a finite idele and a group element such that $W(\mathrm{diag}(a,1)g) = \bigl(\prod_{w'} \rho F_{\mathrm{ref}}(\iota_{w'}(a_{w'}))\bigr) \cdot C(a_{\mathrm{fin}}, g)$ for every idele $a$ and every $g$ with trivial archimedean component.
--
--   This is the local analysis at the real place of the first Fourier–Whittaker coefficient of a cuspidal Casimir eigenform of pure weight: the Whittaker differential equation together with moderate growth on the two connected sheets of the torus, and the resulting factorisation of $W$ into an archimedean factor and a function of the finite part. It feeds the reconstruction of a Whittaker function as a Bessel-type function, used in [`LanglandsTunnell.exists_whittaker_factorization_add_smul_reflect_lower_of_archCasimir_eigenvector_weightOne_of_ne`](thm.html#LanglandsTunnell.exists_whittaker_factorization_add_smul_reflect_lower_of_archCasimir_eigenvector_weightOne_of_ne) on the way to the converse theorem input for Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_torus_peel_ode_growth_and_separation_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_smul.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.InfinitePlace.Completion
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell LanglandsTunnell.Converse NumberField.TateGlobal
open scoped Real

theorem AutomorphicForm.whittakerCoefficient_torus_peel_ode_growth_and_separation_of_isIsotypicCuspFormAt_of_archCasimirAt_eq_smul
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (U : Ideal (𝓞 ℚ) → Subgroup (AdelicGL2 (𝓞 ℚ) ℚ))
    (gen : HeightOneSpectrum (𝓞 ℚ) → AdelicGL2 (𝓞 ℚ) ℚ)
    (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (hψ : IsGlobalAddChar ℚ ψ) (w : InfinitePlace ℚ) (hw : w.IsReal)
    (hψr : ∀ x : InfiniteAdeleRing ℚ, (∀ w' : InfinitePlace ℚ, w' ≠ w → x w' = 0) →
      ψ (⟨x, 0⟩ : AdeleRing (𝓞 ℚ) ℚ) = Complex.exp (2 * Real.pi * Complex.I * extensionEmbedding w (x w)))
    (ξ : (productionPinsOf ℚ D U gen (adelicBox ℚ)).Z →* ℂˣ)
    (N : Ideal (𝓞 ℚ)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (Φ : HeckeEigensystem ℚ ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ
        (productionPinsOf ℚ D U gen (adelicBox ℚ))
        ξ N S Φ φ)
    (hconv : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ α = φ)
    (hsm : IsArchSmoothAt hw φ) (ν : ℂ) (hΩ : archCasimirAt hw φ = (1 / 4 - ν ^ 2) • φ)
    (k : ℤ) (hwt : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw k) φ)
    (uc : ℂ) (ac : ℤ) (hcen : IsArchCompAt ℚ (ξ.comp Subgroup.topEquiv.symm.toMonoidHom) w uc ac)
    (W : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hW : W = whittakerCoefficient ℚ
        (productionPinsOf ℚ D U gen (adelicBox ℚ))
        ψ φ 1)
    (hgr : ∀ t : AdelicGL2 (𝓞 ℚ) ℚ, t ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C M : ℝ, ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).2 = 1 →
        ‖W (diagOne a * t)‖ ≤ C * ideleNorm ℚ a ^ M) :

    ((∀ (X : AdeleRing (𝓞 ℚ) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ), W (unipotentGL2 X * g) = ψ X * W g) ∧
      ∀ (x : ℝ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        W (archRealGLAt hw (unipotentGL2 x) * g) = Complex.exp (2 * Real.pi * Complex.I * x) * W g) ∧

    (∀ (y : ℝ) (hy : 0 < y) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)
        = (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ uc * W (archRealGLAt hw (diagOne (Units.mk0 y hy.ne')) * g)) ∧

    (∀ (y : ℝ) (hy : 0 < y) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)
        = (((Real.sqrt y)⁻¹ : ℝ) : ℂ) ^ uc
            * W (archRealGLAt hw (diagOne (Units.mk0 (-y) (neg_ne_zero.mpr hy.ne'))) * g)) ∧

    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, AdelicLevel.glArch (𝓞 ℚ) ℚ g = 1 →
      (DifferentiableOn ℝ (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
        DifferentiableOn ℝ (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g)))
          (Set.Ioi 0) ∧
        ∀ y : ℝ, 0 < y →
          (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g))) y
              + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * ((k : ℝ) : ℂ) * (y : ℂ) - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
                * W (archRealGLAt hw (splitTorusGL2 (Real.log y / 2)) * g) = 0) ∧
      (DifferentiableOn ℝ
          (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)) (Set.Ioi 0) ∧
        DifferentiableOn ℝ
          (deriv (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g)))
          (Set.Ioi 0) ∧
        ∀ y : ℝ, 0 < y →
          (y : ℂ) ^ 2 * deriv (deriv
                (fun y : ℝ => W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g))) y
              + (1 / 4 - ν ^ 2 + 2 * (π : ℂ) * (((-k : ℤ) : ℝ) : ℂ) * (y : ℂ)
                  - 4 * (π : ℂ) ^ 2 * (y : ℂ) ^ 2)
                * W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log y / 2)) * g) = 0)) ∧

    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z → ‖W (archRealGLAt hw (splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N') ∧

    (∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
      ∃ C' N' : ℝ, ∀ z : ℝ, 1 ≤ z →
        ‖W (archRealGLAt hw (UpperHalfPlane.J * splitTorusGL2 (Real.log z / 2)) * g)‖ ≤ C' * z ^ N') ∧

    (∀ g₀ : AdelicGL2 (𝓞 ℚ) ℚ, W g₀ ≠ 0 →
      ∃ (r : ℝ) (hr : r ≠ 0) (t : AdelicGL2 (𝓞 ℚ) ℚ), t ∈ finiteAdelicGL2Subgroup ℚ ∧
        W (archRealGLAt hw (diagOne (Units.mk0 r hr)) * t) ≠ 0) ∧

    (∀ t₀ : AdelicGL2 (𝓞 ℚ) ℚ, t₀ ∈ finiteAdelicGL2Subgroup ℚ → ∀ (y₀ : ℝ) (hy₀ : 0 < y₀),
      W (archRealGLAt hw (diagOne (Units.mk0 y₀ hy₀.ne')) * t₀) ≠ 0 →
        ∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (y : ℝ) (hy : 0 < y),
          W (archRealGLAt hw (diagOne (Units.mk0 y hy.ne')) * h)
            = W (archRealGLAt hw (diagOne (Units.mk0 y₀ hy₀.ne')) * h)
                / W (archRealGLAt hw (diagOne (Units.mk0 y₀ hy₀.ne')) * t₀)
                * W (archRealGLAt hw (diagOne (Units.mk0 y hy.ne')) * t₀)) ∧

    (∀ (Fref : ℂ → ℂ) (cst : AdelicGL2 (𝓞 ℚ) ℚ → ℂ),
      (∀ h : AdelicGL2 (𝓞 ℚ) ℚ, h ∈ finiteAdelicGL2Subgroup ℚ → ∀ (r : ℝ) (hr : r ≠ 0),
        W (archRealGLAt hw (diagOne (Units.mk0 r hr)) * h) = cst h * Fref (r : ℂ)) →
      ∀ ρ : ℂ, ρ ≠ 0 →
        ∃ C : FiniteAdeleRing (𝓞 ℚ) ℚ → AdelicGL2 (𝓞 ℚ) ℚ → ℂ,
          ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, g ∈ finiteAdelicGL2Subgroup ℚ →
            W (diagOne a * g)
              = (∏ w' : InfinitePlace ℚ, ρ * Fref (extensionEmbedding w' ((a : AdeleRing (𝓞 ℚ) ℚ).1 w')))
                  * C (a : AdeleRing (𝓞 ℚ) ℚ).2 g) := by sorry
