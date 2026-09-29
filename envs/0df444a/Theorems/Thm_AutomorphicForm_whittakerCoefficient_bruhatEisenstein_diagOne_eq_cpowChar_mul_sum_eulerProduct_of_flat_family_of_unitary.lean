-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family_of_unitary
-- name    : AutomorphicForm.whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family_of_unitary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/3576465f-89c6-56cb-8d1c-a2a401bea83c
-- title:
--   Whittaker coefficients of a flat unitary Eisenstein family along the torus
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the homomorphism $(\mathbb{A}_F)^\times \to \mathbb{R}^\times$ obtained from `distribHaarChar` of the adele ring, assumed everywhere positive ($h\alpha$). Fix $\mu,\nu\colon(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ with $|\mu(x)|=|\nu(x)|=1$ and trivial on principal ideles; an additive character $\psi$ of $\mathbb{A}_F$ that is trivial on $F$, continuous and non-trivial; local additive characters $\psi_v$ at the finite places with levels $n_\psi(v)$ (finitely many non-zero) — $\psi_v$ trivial on $\{|x|\le \exp n_\psi(v)\}$ and non-trivial somewhere in $\{|x|\le\exp(n_\psi(v)+1)\}$ — such that $\psi$ on the finite adeles is $\prod_v^{\mathrm{f}}\psi_v$; non-zero archimedean frequencies $\theta_r(i)\in\mathbb{R}$, $\theta_c(w)\in\mathbb{C}$ with $\psi$ on the infinite part equal to $\prod_i e^{-2\pi i\theta_r(i)p_i}\prod_w e^{-4\pi i\,\mathrm{Re}(\theta_c(w)p_w)}$; uniformisers $\varpi_v$ of valuation $\mathrm{ofAdd}(-1)$. Let $\varphi_s$ be a family of functions on $\mathrm{GL}_2(\mathbb{A}_F)$ with $\varphi_s(bg)=\mu(b_{11})\alpha(b_{11})^{s+1/2}\,\nu(b_{22})\alpha(b_{22})^{-(s+1/2)}\varphi_s(g)$ for $b$ in the adelic Borel, archimedean $K$-finite at each infinite place, with open stabiliser inside the subgroup of trivial archimedean part, jointly continuous, holomorphic in $s$, flat (equal values at all $s,s'$ on $k$ whose finite part is integral and whose archimedean components are row isometries), and not identically zero; put $E_s(h)=\varphi_s(h)+\sum_{\xi\in F}\varphi_s(w\,n(\xi)h)$ with $w$ the adelic Weyl element. Write $j_{\mathbb{R}}(k,w,t)=\int_{\mathbb{R}}\bigl((x-i)/\sqrt{1+x^2}\bigr)^k(1+x^2)^{-w}e^{-2\pi itx}\,dx$ and $j_{\mathbb{C}}(a,b,w,\zeta)=\int_{\mathbb{C}}z^a\bar z^{\,b}(1+|z|^2)^{-w}e^{-4\pi i\,\mathrm{Re}(\zeta z)}\,dz$. Then there are a finite set $S$ of finite places, $n\in\mathbb{N}$, entire functions $C_j$, integers $k_{j,i}$ and reals $\tau_{j,i}$ at the real places, triples $(a,b,m)_{j,w}$ with $a+b\le m$ and reals $\tau_{j,w}$ at the complex places, an idele $a$, an adele $u$, thresholds $\mathrm{thr}(v)\in\mathbb{Z}$ vanishing off $S$, and functions $\Phi_{j,v}(w,s)$, entire in $s$, equal to $1$ for $v\notin S$ when $|w|=1$, vanishing when $w\ne0$ and $|w|>\exp\mathrm{thr}(v)$, locally constant in $w$ away from $w=0$, and bounded on $\|s\|\le R$ by $(M$ on $S$, $1$ off $S)$ times $\bigl(N(v)^{(-e)^+}\bigr)^{\kappa}$ when $|w|=\exp e$, with $M\ge0$ and $\kappa$ depending only on $R$, such that for $\mathrm{Re}\,s>1$, every $\xi\in F^\times$ and every idele $y$ the Whittaker coefficient of $E_s$ at $\xi$ and $\mathrm{diag}(y,1)$, taken with respect to `productionPins` and $\psi$, equals $\nu(y)\,\alpha(y)^{1/2-s}$ times $\sum_{j}C_j(s)$ multiplied by $\bigl(2^{r_2}/\sqrt{|d_F|}\bigr)\,\mathrm{distribHaarChar}(a)^{-1}\psi(\xi y u)$, by $\prod_i j_{\mathbb{R}}\bigl(k_{j,i},\,s+\tfrac12+i\tau_{j,i}/2,\,-\theta_r(i)(\xi y a^{-1})_i\bigr)$, by $\prod_w j_{\mathbb{C}}\bigl(a_{j,w},b_{j,w},\,2s+1+m_{j,w}/2+i\tau_{j,w}/2,\,-\theta_c(w)(\xi y a^{-1})_w\bigr)$, and by $\prod_{v\notin S}\bigl(1-\chi_v(\varpi_v)N(v)^{-(2s+1)}\bigr)\cdot\prod^{\mathrm{f}}_v\Phi_{j,v}\bigl((\xi y a^{-1})_v,s\bigr)$, where $\chi_v$ is the local component of $\mu\nu^{-1}$ at $v$.
--
--   This is the explicit Euler-product form of the Jacquet–Whittaker integral of a flat, $K$-finite Eisenstein section of $\mathrm{GL}_2$ over a number field, induced from the unitary idele-class characters $\mu\alpha^{s+1/2}$ and $\nu\alpha^{-(s+1/2)}$ and evaluated along the split torus: the archimedean factors appear as absolutely convergent weight integrals, the inverse partial $L$-function $\prod_{v\notin S}(1-\chi_v(\varpi_v)N(v)^{-(2s+1)})$ is displayed, and the finite local factors are packaged with entirety, support, growth and local-constancy properties. It is the input to the statements continuing these Whittaker coefficients in $s$ and exhibiting them as an Euler product times an entire function.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family_of_unitary.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.InfinitePlace AutomorphicForm
open AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

open scoped Classical in

theorem AutomorphicForm.whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family_of_unitary (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
      (ψv : (v : HeightOneSpectrum (𝓞 F)) → AddChar (v.adicCompletion F) ℂ)
      (nψ : HeightOneSpectrum (𝓞 F) → ℤ)
      (_hnψfin : (Function.support nψ).Finite)
      (_hψv : ∀ (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F),
        Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
      (_hψv' : ∀ v : HeightOneSpectrum (𝓞 F),
        ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
      (_hψfin : ∀ x : FiniteAdeleRing (𝓞 F) F,
        ψ (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F) x)
        = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ψv v (x v))
      (θr : {w : InfinitePlace F // w.IsReal} → ℝ) (_hθr : ∀ i, θr i ≠ 0)
      (θc : {w : InfinitePlace F // w.IsComplex} → ℂ) (_hθc : ∀ w, θc w ≠ 0)
      (_hψarch : ∀ p : mixedEmbedding.mixedSpace F,
        ψ (AddMonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
        ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm p))
        = (∏ i : {w : InfinitePlace F // w.IsReal},
        Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
        * ∏ w : {w : InfinitePlace F // w.IsComplex},
        Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (_hφne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let jR : ℤ → ℂ → ℝ → ℂ := fun k w t => ∫ x : ℝ,
      ((((x : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + x ^ 2) : ℝ) : ℂ)) ^ k
          * (((1 + x ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I))
    let jC : ℕ → ℕ → ℂ → ℂ → ℂ := fun a b w ζ => ∫ z : ℂ,
      z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (n : ℕ) (C : Fin n → ℂ → ℂ)
      (kdat : Fin n → {w : InfinitePlace F // w.IsReal} → ℤ)
      (τr : Fin n → {w : InfinitePlace F // w.IsReal} → ℝ)
      (abm : Fin n → {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
      (τc : Fin n → {w : InfinitePlace F // w.IsComplex} → ℝ)
      (a : (AdeleRing (𝓞 F) F)ˣ) (u : AdeleRing (𝓞 F) F)
      (thr : HeightOneSpectrum (𝓞 F) → ℤ)
      (Φ : Fin n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ),
      (∀ j, Differentiable ℂ (C j)) ∧
      (∀ (j : Fin n) (w : {w : InfinitePlace F // w.IsComplex}),
        (abm j w).1 + (abm j w).2.1 ≤ (abm j w).2.2) ∧
      (∀ v ∉ S, thr v = 0) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w)) ∧
      (∀ (j : Fin n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F) (s : ℂ), w ≠ 0 →
        WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0) ∧
      (∀ R : ℝ, ∃ (M : ℝ) (κ : ℕ), 0 ≤ M ∧ ∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F))
        (w : v.adicCompletion F) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
          ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ) ∧
      (∀ (j : Fin n) (v : HeightOneSpectrum (𝓞 F)) (w₀ : v.adicCompletion F), w₀ ≠ 0 → ∃ δ : ℤ,
        ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s) ∧
      ∀ (s : ℂ), 1 < s.re → ∀ (ξ : F), ξ ≠ 0 → ∀ y : (AdeleRing (𝓞 F) F)ˣ,
        whittakerCoefficient F (productionPins F) ψ (E s) ξ (diagOne y)
          = ((ν y : ℂˣ) : ℂ) * ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ)
            * ∑ j : Fin n, C j s
              * ((((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
                  * ((((distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ≥0) : ℝ) : ℂ)⁻¹
                  * ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F) * u)))
              * (∏ i : {w : InfinitePlace F // w.IsReal},
                  jR (kdat j i) (s + 1 / 2 + ((τr j i : ℝ) : ℂ) * Complex.I / 2)
                    (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
                      (algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F)
                        * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i)))
              * (∏ w : {w : InfinitePlace F // w.IsComplex},
                  jC (abm j w).1 (abm j w).2.1
                    (2 * s + 1 + ((abm j w).2.2 : ℂ) / 2 + ((τc j w : ℝ) : ℂ) * Complex.I / 2)
                    (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
                      (algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F)
                        * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w)))
              * ((∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                  (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
                * ∏ᶠ v : HeightOneSpectrum (𝓞 F),
                    Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F)
                        * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s) := by sorry
