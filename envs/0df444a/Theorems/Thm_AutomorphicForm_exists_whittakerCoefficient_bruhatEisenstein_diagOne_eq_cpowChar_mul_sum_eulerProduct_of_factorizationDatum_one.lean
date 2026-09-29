-- Prove2me | Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_factorizationDatum_one
-- name    : AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_factorizationDatum_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/169d5630-4b76-551c-a275-004e134cbcf5
-- title:
--   Torus Whittaker coefficients of a Bruhat–Eisenstein series via factorisation datum
-- statement:
--   Throughout, $F$ is a number field, $\mathbb{A}_F$ denotes `AdeleRing (𝓞 F) F`, and $\alpha : \mathbb{A}_F^\times \to \mathbb{R}^\times$ is the module character obtained from `distribHaarChar (AdeleRing (𝓞 F) F)` by composing the scaling factor in $\mathbb{R}_{\ge 0}$ with the inclusion into $\mathbb{R}$ and passing to units; for a parameter $s$, `cpowChar α hα s` is the character $y \mapsto \alpha(y)^{s}$ with values in $\mathbb{C}^\times$.
--
--   The assertion begins with data depending on $F$ alone: there exist functions $d, \mu_{\mathcal O} : \mathrm{HeightOneSpectrum}(\mathcal O_F) \to \mathbb{R}$ and, for each finite place $v$, a measure $\lambda_v$ on the completion $F_v$ (with respect to the Borel $\sigma$-algebra of its topology), such that $d_v \ge 1$ and $\mu_{\mathcal O,v} > 0$ for every $v$, and such that the following holds for every choice of the remaining data.
--
--   Those remaining data and hypotheses are: the positivity hypothesis `hα` that $\alpha(t) > 0$ for every idele $t$; two characters $\mu, \nu : \mathbb{A}_F^\times \to \mathbb{C}^\times$ which are unitary ($\|\mu(x)\| = \|\nu(x)\| = 1$ for all $x$) and trivial on the principal ideles $F^\times$; an additive character $\psi$ of $\mathbb{A}_F$ which is trivial on $F$, continuous and non-trivial; local additive characters $\psi_v$ of each $F_v$ together with exponents $n_\psi(v) \in \mathbb{Z}$ of finite support, such that $\psi_v$ is trivial on $\{x : v(x) \le \exp(n_\psi(v))\}$ and non-trivial on the next ball (some $x$ with $v(x) \le \exp(n_\psi(v)+1)$ has $\psi_v(x) \ne 1$), and such that on the finite adeles $\psi$ is the finite product $\prod_v \psi_v(x_v)$; archimedean parameters $\theta_r(i) \in \mathbb{R} \setminus \{0\}$ for the real places and $\theta_c(w) \in \mathbb{C} \setminus \{0\}$ for the complex places, together with the hypothesis `_hψarch` expressing $\psi$ on the infinite part, in mixed-space coordinates, as $\prod_i \exp(-2\pi i\,\theta_r(i) p_i) \cdot \prod_w \exp(-4\pi i\,\mathrm{Re}(\theta_c(w) p_w))$; uniformisers $\varpi_v \in F_v^\times$ with $v(\varpi_v) = \mathrm{ofAdd}(-1)$; and a family $\varphi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ subject to the hypotheses: for each $s$, $\varphi_s$ is a section of the induced representation in the sense of `IsInducedSection`, i.e. $\varphi_s(bg) = \eta_1(b_{11})\,\eta_2(b_{22})\,\varphi_s(g)$ for $b$ in the adelic Borel subgroup, with $\eta_1 = \mu\cdot\alpha^{s+1/2}$ and $\eta_2 = \nu\cdot\alpha^{-(s+1/2)}$; $\varphi_s$ is archimedean $K$-finite (`IsArchKFinite`: at each infinite place $w$ the predicate `RightTranslatesSpanFinite` holds for the row-isometry subgroup at $w$) and $K_f$-smooth (`IsKfSmooth`: its stabiliser under right translation inside the kernel of `glArch`, the ideles with trivial archimedean component, is open); $\varphi$ is jointly continuous in $(s,g)$ and holomorphic in $s$ for each $g$; $\varphi$ is flat, i.e. $\varphi_s(k) = \varphi_{s'}(k)$ for all $s, s'$ whenever the finite part of $k$ lies in `finiteIntegralGL2` and every archimedean component of $k$ is a row isometry (unit determinant norm and preservation of $\|x\|^2+\|y\|^2$ under the row action); and $\varphi$ is not identically zero. Finally there are a finite set $S$ of finite places and a datum $D$ of type [`EisensteinGeneral.Piece.FactorizationDatum F ψv nψ (μ * ν⁻¹) ϖ φ 1 S`](def/EisensteinGeneral_FactorizationDatum.html#L13), that is, a factorisation datum for $\varphi$ at the identity of $\mathrm{GL}_2(\mathbb{A}_F)$ relative to $S$, consisting of a conductor function $c_S$ and an integer $m_S \ge 1$, a number $n = D.n$ of pieces, local integrands $A_{j,v}, B_{j,v}, h_{j,v}$, archimedean exponents $\mathrm{kdat}$, $\tau_r$ on the real places and triples $\mathrm{abm}$, $\tau_c$ on the complex places, archimedean kernels $W_r, W_c$, an idele $D.a$, an adele $D.u$ and coefficient functions $C_j$, together with the structure's compatibility clauses (unitarity and off-$S$ unramifiedness of the local characters of $\mu\nu^{-1}$, triviality of $n_\psi$ and the prescribed off-$S$ shape of $h_{j,v}$, triviality of the character on the higher unit groups of level $c_S(v)$, and local constancy of $A_{j,v}$, $B_{j,v}$ at level $m_S$).
--
--   Three abbreviations are introduced. First, the Bruhat–Eisenstein series $E_s(h) = \varphi_s(h) + \sum_{\xi \in F} \varphi_s(w\, u(\xi)\, h)$, where $w$ is the adelic image of the antidiagonal Weyl element and $u(\xi)$ the upper unipotent matrix with entry $\xi$. Second, the archimedean integrals
--   $$jR(k,w,t) = \int_{\mathbb{R}} \Bigl(\tfrac{x - i}{\sqrt{1+x^2}}\Bigr)^{k} (1+x^2)^{-w} e^{-2\pi i t x}\,dx, \qquad jC(a,b,w,\zeta) = \int_{\mathbb{C}} z^{a}\bar z^{b} (1+\|z\|^2)^{-w} e^{-4\pi i\,\mathrm{Re}(\zeta z)}\,dz.$$
--   Third, the thresholds $\mathrm{thr}_v = n_\psi(v) + \max(m_S, c_S(v))$ for $v \in S$ and $\mathrm{thr}_v = 0$ otherwise.
--
--   The conclusion is the existence of local factors $\Phi_j : \prod_v (F_v \to \mathbb{C} \to \mathbb{C})$, indexed by $j \in \mathrm{Fin}\,D.n$, with the following eleven properties.
--
--   (i) For $v \notin S$, $\Phi_j(v,w,s) = \mathrm{corrOff}(\chi_v(\varpi_v), N(v), e, s)$ where $\chi = \mu\nu^{-1}$, $\chi_v$ is its local character [`NumberField.TateGlobal.localChar`](def/NumberField_TateGlobalZeta.html#L31), $N(v) = \mathrm{absNorm}(v)$ and $e = \mathrm{WithZero.log}(v(w))$; here $\mathrm{corrOff}$ equals $\sum_{k=0}^{(-e)} (\chi_v(\varpi_v) N(v)^{-2s})^{k}$ when $e \le 0$ and $0$ otherwise.
--
--   (ii) For $v \in S$ and every $w \in F_v$ there are $\gamma_0 \in \mathbb{C}$ and a sequence $\mathrm{sh} : \mathbb{N} \to \mathbb{C}$ such that $\|\gamma_0\| \le \int_{\mathcal O_v} \|A_{j,v}(x)\|\,d\lambda_v$, such that for every $k \ge 1$
--   $$\|\mathrm{sh}(k)\| \le \Bigl(\int_{F_v} \bigl(\|\mathbf 1_{\mathcal O_v} A_{j,v}(x)\| + \mathbf 1_{F_v \setminus \mathcal O_v}(x)\,(|x|_v^{-1})^{3}\,\|B_{j,v}(x^{-1})\|\bigr) d\lambda_v\Bigr)\, d_v^{\,k},$$
--   where $|\cdot|_v$ is [`LanglandsTunnell.TateLocal.modulus`](def/LanglandsTunnell_TateLocalZeta.html#L15), and such that for all $s$, $\Phi_j(v,w,s) = \mathrm{corrOn}(N(v), n_\psi(v), c_S(v), m_S, e, \mu_{\mathcal O,v}, \gamma_0, \mathrm{sh}, s)$; the latter vanishes unless $e \le n_\psi(v) + \max(m_S, c_S(v))$, in which case it equals $\mu_{\mathcal O,v}^{-1}\bigl(\gamma_0 + \sum_{k=1}^{K} (N(v)^{-(2s+1)})^{k}\mathrm{sh}(k)\bigr)$ with $K = \max(m_S - 1,\ n_\psi(v) + c_S(v) - e)$ truncated to $\mathbb{N}$.
--
--   (iii) Each coefficient function $C_j$ is entire. (iv) For every $j$ and every complex place $w$, the triple $\mathrm{abm}_j(w) = (a,b,m)$ satisfies $a + b \le m$. (v) $\mathrm{thr}_v = 0$ for $v \notin S$. (vi) Each $\Phi_j(v,w,\cdot)$ is entire in $s$. (vii) For $v \notin S$ and $v(w) = 1$, $\Phi_j(v,w,s) = 1$. (viii) For every $j, v$ and every $w \ne 0$ with $\exp(\mathrm{thr}_v) < v(w)$, $\Phi_j(v,w,s) = 0$. (ix) For every $R$ there are $M \ge 0$ and $\kappa \in \mathbb{N}$ such that for all $j, v$, all $w$ with $v(w) = \exp(e)$ and all $s$ with $\|s\| \le R$,
--   $$\|\Phi_j(v,w,s)\| \le (\text{$M$ if } v \in S \text{, else } 1)\cdot \bigl(N(v)^{(-e)^+}\bigr)^{\kappa}.$$
--   (x) For every $j, v$ and every $w_0 \ne 0$ there is $\delta \in \mathbb{Z}$ with $\Phi_j(v,w,s) = \Phi_j(v,w_0,s)$ for all $s$ whenever $v(w - w_0) \le \exp(\delta)$.
--
--   (xi) The Whittaker identity: for every $s$ with $\mathrm{Re}\,s > 1$, every $\xi \in F$ with $\xi \ne 0$ and every idele $y$, the Whittaker coefficient of $E_s$ at $\xi$ evaluated at the torus element $\mathrm{diag}(y,1)$ — that is, $\int_{\mathbb{A}_F} E_s(u(x)\,\mathrm{diag}(y,1))\,\psi(-\xi x)\,d\nu(x)$ with $\nu$ the measure pinned by `productionPins F`, namely additive Haar measure on $\mathbb{A}_F$ conditioned on the box `adelicBox F` — equals
--   $$\nu(y)\,\alpha(y)^{1/2 - s} \sum_{j} C_j(s)\cdot \Bigl(\tfrac{2^{r_2}}{\sqrt{|\mathrm{disc}\,F|}}\cdot \mathrm{distribHaarChar}(\mathbb{A}_F)(D.a)^{-1}\,\psi(\xi\, y\, D.u)\Bigr) \cdot P_{\mathbb{R}} \cdot P_{\mathbb{C}} \cdot P_{\mathrm{fin}},$$
--   where $r_2$ is the number of complex places; $P_{\mathbb{R}} = \prod_{i \text{ real}} jR\bigl(\mathrm{kdat}_j(i),\, s + 1/2 + i\,\tau_{r,j}(i)/2,\, -\theta_r(i)\,x_i\bigr)$ and $P_{\mathbb{C}} = \prod_{w \text{ complex}} jC\bigl(a,\, b,\, 2s + 1 + m/2 + i\,\tau_{c,j}(w)/2,\, -\theta_c(w)\,x_w\bigr)$ with $(a,b,m) = \mathrm{abm}_j(w)$ and with $x_i$, $x_w$ the real and complex mixed-space coordinates of the infinite part of the adele $\xi\, y\, D.a^{-1}$; and
--   $$P_{\mathrm{fin}} = \Bigl(\prod_{v \notin S} \bigl(1 - \chi_v(\varpi_v)\,N(v)^{-(2s+1)}\bigr)\Bigr)\cdot \prod_v \Phi_j\bigl(v,\, (\xi\, y\, D.a^{-1})_v,\, s\bigr),$$
--   the first product being a convergent infinite product over the places outside $S$ and the second a finite product (in the sense of `finprod`) over all finite places, evaluated at the $v$-component of the finite part of $\xi\, y\, D.a^{-1}$.
--
--   The quantifier order is the content of the uniformity claim: the local measures $\lambda_v$, the volumes $\mu_{\mathcal O,v} > 0$ and the ratios $d_v \ge 1$ occurring in the bounds of clause (ii) are fixed before the characters, the additive data, the family $\varphi$, the set $S$ and the datum $D$ are chosen.
--
--   This is the torus Whittaker (Fourier) expansion of a Bruhat–Eisenstein series on $\mathrm{GL}_2$ over a number field, in the Tate-style factorised form: a finite sum of products of archimedean $K$-type integrals with a global Euler product whose local factors are the explicit truncated geometric sums `corrOff` off the bad set and the ramified sums `corrOn` on it, with norm bounds for the ramified coefficients expressed through the integrands of the factorisation datum. It is the input to the uniform version [`AutomorphicForm.exists_forall_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_norm_le_on_balls_and_of_re_mem_Icc_of_flat`](thm.html#AutomorphicForm.exists_forall_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_norm_le_on_balls_and_of_re_mem_Icc_of_flat), where the explicit local factors are estimated on balls in the spectral parameter.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_factorizationDatum_one.lean

import Definitions.Def_EisensteinGeneral_FactorizationDatum
import Definitions.Def_EisensteinGeneral_LocalCorrection
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

theorem AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_factorizationDatum_one (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∃ (d μ𝒪 : HeightOneSpectrum (𝓞 F) → ℝ)
      (lam : (v : HeightOneSpectrum (𝓞 F)) → @MeasureTheory.Measure (v.adicCompletion F) (borel _)),
      (∀ v, 1 ≤ d v) ∧ (∀ v, 0 < μ𝒪 v) ∧
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
      (_hφne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), φ s g ≠ 0)
      (S : Finset (HeightOneSpectrum (𝓞 F)))
      (D : EisensteinGeneral.Piece.FactorizationDatum F ψv nψ (μ * ν⁻¹) ϖ φ (1 : AdelicGL2 (𝓞 F) F) S),
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
    let thr : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
      if v ∈ S then nψ v + ((max D.mS (D.cS v) : ℕ) : ℤ) else 0
    ∃ (Φ : Fin D.n → (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ → ℂ),

      (∀ (j : Fin D.n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ),
        Φ j v w s = EisensteinGeneral.LocalCorrection.corrOff
          ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v (ϖ v) : ℂˣ) : ℂ) (Ideal.absNorm v.asIdeal)
          (WithZero.log (Valued.v w)) s) ∧

      (∀ (j : Fin D.n), ∀ v ∈ S, ∀ (w : v.adicCompletion F), ∃ (γ₀ : ℂ) (sh : ℕ → ℂ),
        ‖γ₀‖ ≤ (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), ‖D.A j v x‖ ∂(lam v)) ∧
        (∀ k : ℕ, 1 ≤ k → ‖sh k‖ ≤
          (∫ x, (‖(v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (D.A j v) x‖
              + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
                  (fun y => ((LanglandsTunnell.TateLocal.modulus y : ℝ))⁻¹ ^ 3 * ‖D.B j v y⁻¹‖) x) ∂(lam v))
            * d v ^ k) ∧
        ∀ s : ℂ, Φ j v w s = EisensteinGeneral.LocalCorrection.corrOn (Ideal.absNorm v.asIdeal) (nψ v) (D.cS v) D.mS
          (WithZero.log (Valued.v w)) (μ𝒪 v) γ₀ sh s) ∧
      (∀ j, Differentiable ℂ (D.C j)) ∧
      (∀ (j : Fin D.n) (w : {w : InfinitePlace F // w.IsComplex}),
        (D.abm j w).1 + (D.abm j w).2.1 ≤ (D.abm j w).2.2) ∧
      (∀ v ∉ S, thr v = 0) ∧
      (∀ (j : Fin D.n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F), Differentiable ℂ (Φ j v w)) ∧
      (∀ (j : Fin D.n), ∀ v ∉ S, ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v w = 1 → Φ j v w s = 1) ∧
      (∀ (j : Fin D.n) (v : HeightOneSpectrum (𝓞 F)) (w : v.adicCompletion F) (s : ℂ), w ≠ 0 →
        WithZero.exp (thr v) < Valued.v w → Φ j v w s = 0) ∧
      (∀ R : ℝ, ∃ (M : ℝ) (κ : ℕ), 0 ≤ M ∧ ∀ (j : Fin D.n) (v : HeightOneSpectrum (𝓞 F))
        (w : v.adicCompletion F) (e : ℤ) (s : ℂ), ‖s‖ ≤ R → Valued.v w = WithZero.exp e →
          ‖Φ j v w s‖ ≤ (if v ∈ S then M else 1) * (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-e).toNat) ^ κ) ∧
      (∀ (j : Fin D.n) (v : HeightOneSpectrum (𝓞 F)) (w₀ : v.adicCompletion F), w₀ ≠ 0 → ∃ δ : ℤ,
        ∀ (w : v.adicCompletion F) (s : ℂ), Valued.v (w - w₀) ≤ WithZero.exp δ → Φ j v w s = Φ j v w₀ s) ∧
      ∀ (s : ℂ), 1 < s.re → ∀ (ξ : F), ξ ≠ 0 → ∀ y : (AdeleRing (𝓞 F) F)ˣ,
        whittakerCoefficient F (productionPins F) ψ (E s) ξ (diagOne y)
          = ((ν y : ℂˣ) : ℂ) * ((cpowChar α hα (1 / 2 - s) y : ℂˣ) : ℂ)
            * ∑ j : Fin D.n, D.C j s
              * ((((2 : ℝ) ^ nrComplexPlaces F / Real.sqrt |(discr F : ℝ)| : ℝ) : ℂ)
                  * ((((distribHaarChar (AdeleRing (𝓞 F) F) D.a : ℝ≥0) : ℝ) : ℂ)⁻¹
                  * ψ (algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F) * D.u)))
              * (∏ i : {w : InfinitePlace F // w.IsReal},
                  jR (D.kdat j i) (s + 1 / 2 + ((D.τr j i : ℝ) : ℂ) * Complex.I / 2)
                    (-(θr i * (InfiniteAdeleRing.ringEquiv_mixedSpace F
                      (algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F)
                        * ((D.a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).1 i)))
              * (∏ w : {w : InfinitePlace F // w.IsComplex},
                  jC (D.abm j w).1 (D.abm j w).2.1
                    (2 * s + 1 + ((D.abm j w).2.2 : ℂ) / 2 + ((D.τc j w : ℝ) : ℂ) * Complex.I / 2)
                    (-(θc w * (InfiniteAdeleRing.ringEquiv_mixedSpace F
                      (algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F)
                        * ((D.a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1).2 w)))
              * ((∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                  (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))))
                * ∏ᶠ v : HeightOneSpectrum (𝓞 F),
                    Φ j v ((algebraMap F (AdeleRing (𝓞 F) F) ξ * (y : AdeleRing (𝓞 F) F)
                        * ((D.a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v) s) := by sorry
