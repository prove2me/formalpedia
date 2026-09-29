-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion
-- name    : AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/00f34968-2dde-5478-b0dc-37d64fd1210c
-- title:
--   Euler factorisation of the unfolded Rankin–Selberg quotient integral
-- statement:
--   Let $K$ be a number field and let $\alpha$ be the character of the idele group $(\mathbb{A}_K)^\times$ with values in $\mathbb{R}^\times$ obtained from the module `distribHaarChar` of the adele ring, with $\alpha$ assumed everywhere positive (hypothesis $h\alpha$). Fix a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_K)$, a family $U$ of subgroups indexed by ideals of $\mathcal{O}_K$ and a family `gen` of elements indexed by the finite places; these enter only through the record `productionPinsOf K D U gen (adelicBox K)`, which equips $\mathrm{GL}_2(\mathbb{A}_K)$ with its Borel structure and Haar measure, takes the full central subgroup, and equips $\mathbb{A}_K$ with the Haar measure conditioned on the box `adelicBox K`. Fix an additive character $\psi$ of $\mathbb{A}_K$ which is trivial on $K$, continuous and nontrivial; characters $\mu,\nu,\omega_x,\omega_y$ of $(\mathbb{A}_K)^\times$ with values in $\mathbb{C}^\times$ and a real $w$, with $\mu,\nu$ of absolute value $1$ everywhere, trivial on principal ideles, and with $\omega_x(z)\overline{\omega_y(z)}\mu(z)\nu(z) = \lVert z\rVert^{2w}$ for all $z$, where $\lVert\cdot\rVert$ is `ideleNorm`. Let $x,y : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous, invariant under left multiplication by the image of $\mathrm{GL}_2(K)$, and satisfy $x(z\cdot g) = \omega_x(z)x(g)$, $y(z\cdot g) = \omega_y(z)y(g)$ for central scalars $z$. Let $S$ be a finite set of finite places such that $x$ and $y$ are invariant under right multiplication by the image of $\mathrm{GL}_2(\mathcal{O}_v)$ for $v \notin S$. Let $l_x,o_x,l_y,o_y$ be complex-valued functions of the finite places and $\kappa$ real, with all four bounded by $N(v)^\kappa$ in absolute value for $v \notin S$. Write $P(g) = W(g)\overline{W'(g)}$, where $W$, $W'$ are the Whittaker coefficients `whittakerCoefficient` of $x$, $y$ at $\alpha = 1$ with respect to $\psi$ and the above pins. Assume that for $v \notin S$ and every $g$ with $\lvert \det g\rvert_v = \max(\lvert g_{10}\rvert_v, \lvert g_{11}\rvert_v)^2$ one has, for all $m \in \mathbb{N}$, $P(a(\varpi_v)^m g) = u_m u'_m P(g)$ with $u_m =$ `heckeRecursionSeq` $N(v)\,(l_x v)\,(o_x v)\,m$ and $u'_m$ the same with $l_y, o_y$, where $a(\varpi_v) =$ `heckeGen`, and that $P(a(\varpi_v)^{-m}g) = 0$ for $m > 0$. Then there is $\sigma_0 \in \mathbb{R}$ such that for every $s$ with $\operatorname{Re} s > \sigma_0$, every continuous $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ which is an induced section for the pair of characters $\mu\,\alpha^{s+1/2}$, $\nu\,\alpha^{-(s+1/2)}$ (that is, $\varphi(bg) = \mu\alpha^{s+1/2}(b_{00})\,\nu\alpha^{-(s+1/2)}(b_{11})\,\varphi(g)$ for $b$ in the adelic Borel subgroup) and is invariant under right multiplication by the image of $\mathrm{GL}_2(\mathcal{O}_v)$ for $v \notin S$, and all reals $d_1,d_2$ for which the quotient integrand is integrable on the quotient of $\mathrm{GL}_2(\mathbb{A}_K)$ by $Z(K)N(\mathbb{A}_K)$ against `rationalCentreUnipotentQuotientMeasure`, there exists $\mathrm{Prod} \in \mathbb{C}$ such that, setting $y_v = \mu(\hat\varpi_v)\,N(v)^{(1/2+w)-s}$ with $\hat\varpi_v$ the idele `uniformizerIdele`, the family indexed by the places $v \notin S$ with terms $$\bigl(1 - o_x(v)o_y(v)\,(y_v/N(v))^2\bigr)\big/ \mathrm{rsEulerPoly}\bigl(l_x(v),\,N(v)o_x(v),\,l_y(v),\,N(v)o_y(v),\,0\bigr)(y_v/N(v)^2)$$ is multipliable with product $\mathrm{Prod}$ (in the sense of `HasProd`), and the quotient integral `quotientIntegral` equals the integral `sPartIntegral` over the locus where the above shell condition holds at every $v \notin S$, multiplied by $\mathrm{Prod}$.
--
--   This is the Euler-factorisation step of the Rankin–Selberg method for $\mathrm{GL}(2) \times \mathrm{GL}(2)$: after unfolding, the integral over the quotient by the rational centre and the unipotent radical splits as the integral over the shell-zero locus outside $S$ times an Euler product over the places outside $S$, whose factors are built from the two Hecke recursion tables. The data are left universally quantified so that both the diagonal (Petersson) instance and the pair instance can use it; it is invoked by the two results constructing test data for which the difference of the Rankin–Selberg integral and the relevant Petersson integral is analytic near the critical point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion.lean

import Definitions.Def_AutomorphicForm_RankinSelbergQuotientIntegral
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm IsDedekindDomain UnramifiedWhittaker
open scoped NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.RankinSelberg.exists_hasProd_quotientIntegral_eq_sPartIntegral_mul_of_shell_recursion
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
      (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
      (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (_hψ : IsGlobalAddChar K ψ)
      (μ ν ωx ωy : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hZ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
          ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))
      (_hμF : IsIdeleClassChar (𝓞 K) K μ) (_hνF : IsIdeleClassChar (𝓞 K) K ν)
      (x y : AdelicGL2 (𝓞 K) K → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        x (globalPoints (𝓞 K) K γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K),
        y (globalPoints (𝓞 K) K γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (_hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), x (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x g)
      (_hyZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K), y (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y g)
      (S : Finset (HeightOneSpectrum (𝓞 K)))
      (_hxK : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          x (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g)
      (_hyK : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
          y (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = y g)
      (lx ox ly oy : HeightOneSpectrum (𝓞 K) → ℂ) (κ : ℝ)
      (_hbd : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ‖lx v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖ox v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧
        ‖ly v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖oy v‖ ≤ ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ κ)
      (_hP : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ,
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 ((heckeGen (𝓞 K) K v) ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1
              ((heckeGen (𝓞 K) K v) ^ m * g)) =
          heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (lx v) (ox v) m *
            heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (ly v) (oy v) m *
            (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 g *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1 g)))
      (_hPneg : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
        Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
          (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
               (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 →
        ∀ m : ℕ, 0 < m →
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ x 1 ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) *
            (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ y 1
              ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g)) = 0),
    ∃ σ₀ : ℝ, ∀ (s : ℂ), σ₀ < s.re →
      ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ α hα s) (etaSnd ν α hα s) φ → Continuous φ →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
          ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
            φ (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g) →
        ∀ (d₁ d₂ : ℝ), Integrable (fun q : RationalCentreUnipotentQuotient K =>
            RankinSelberg.quotientIntegrand K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ q.out)
          (rationalCentreUnipotentQuotientMeasure K) →
        ∃ Prod : ℂ,
          HasProd (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
            (1 - ox v.1 * oy v.1 *
                ((((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
                    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 / 2 + w : ℂ) - s)) /
                  ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ)) ^ 2) /
              (LanglandsTunnell.RankinSelberg.rsEulerPoly (lx v.1) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) * ox v.1)
                  (ly v.1) (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) * oy v.1) 0).eval
                ((((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
                    ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 / 2 + w : ℂ) - s)) /
                  ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ 2)) Prod ∧
          RankinSelberg.quotientIntegral K (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ =
            RankinSelberg.sPartIntegral K S (productionPinsOf K D U gen (adelicBox K)) ψ x y φ w d₁ d₂ * Prod := by sorry
