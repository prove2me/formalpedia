-- Prove2me | Theorems.Thm_AutomorphicForm_exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat
-- name    : AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/fc18c897-34b2-5a89-8a81-5b67a711cc42
-- title:
--   Rankin–Selberg package for Theta×̃Theta over ℚ
-- statement:
--   Fix reals $c,u,d_1,d_2$ with $0<c$, $0<d_1<d_2$ and a finite set $T\subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb Q})$, and let $D_T=\bigcup_{x\in T}\{g x : g\in \Sigma\}$, where $\Sigma$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$ (finite part integral, all archimedean local heights $\ge c$, all archimedean window quantities $\le u^2$, all archimedean determinant norms in $[d_1,d_2]$). Assume $D_T$ covers modulo the centre: every $g$ admits $\gamma\in\mathrm{GL}_2(\mathbb Q)$ and an idele $z$ with $\gamma g z\in D_T$. Let $\Theta$ be a Hecke eigensystem over $\mathbb Q$ with values in $\mathbb C$ (a nonzero level ideal together with tables $a,b$ on the finite places), and assume `IsArithGenuineCuspRealizable`, i.e. the recentred eigensystem $\Theta.\mathtt{toRawCentral}$ (same $a$, with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$) admits a genuine smooth cusp realisation at the production pins built from the carrier $D_T$, the levels $N\mapsto \mathrm{levelOne}(N)\sqcap\ker(\text{archimedean component})$, the Hecke generators $v\mapsto \mathrm{heckeGen}\,v$, the Borel adelic Haar measures on $\mathrm{GL}_2$ and on the adeles conditioned on the adelic box, and central subgroup $\top$. Then there exist a finite set $S$ of primes, reals $\sigma_0$ and $x<0$, a Haar measure $\nu_0$ on the idele group, a set $D\subseteq\mathrm{GL}_2(\mathbb A_{\mathbb Q})$, an integer $n$, coefficients $\mathrm{coef}:\mathrm{Fin}\,n\to\mathbb C$, functions $\varphi_i,\varphi_i'$ on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$, Schwartz–Bruhat functions $\Phi_i$ on $\mathbb A_{\mathbb Q}^2$ (elements of the span of pure tensors), functions $Z_r,H:\mathbb C\to\mathbb C$ and constants $c_1,c_0$ such that: $Z_r$ is entire; for $\operatorname{Re} s>\sigma_0$ the sum $\sum_i \mathrm{coef}_i\int_D \varphi_i\varphi_i'\,E(\Phi_i,s-\tfrac12)$ of Rankin–Selberg integrals against the Godement–Eisenstein series at the trivial pair of characters and the module character of the ideles equals $Z_r(s)+c_1/(s-1)+c_0/s$; $H$ is analytic at every real point $\sigma>x$; $c_0=0$ or $H(0)=0$; and for $\operatorname{Re} s>\sigma_0$ the family of inverse Euler factors $\bigl(\mathrm{rsEulerPoly}(a_v/b_v,\,b_v^{-1},\,a_v,\,b_v,\,0)(N(v)^{-s})\bigr)^{-1}$ over the primes $v\notin S$ has product $\bigl(Z_r(s)+c_1/(s-1)+c_0/s\bigr)\,H(s)$.
--
--   This is the integral-representation package for the Rankin–Selberg $L$-function $L^S(s,\Theta\times\widetilde\Theta)$ over $\mathbb Q$: the global $\mathrm{GL}_2\times\mathrm{GL}_2$ integral against the Eisenstein series of a Godement section is exhibited as an entire function plus simple polar terms at $s=1$ and $s=0$, and, after multiplication by the factor $H$ accounting for the omitted places, as the partial Euler product of the degree-six Rankin–Selberg polynomials. It feeds the analytic continuation statement [`AutomorphicForm.exists_finset_neg_analyticAt_ofReal_hasProd_rsEulerPoly_self_div_sub_one_rat`](thm.html#AutomorphicForm.exists_finset_neg_analyticAt_ofReal_hasProd_rsEulerPoly_self_div_sub_one_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

open IsDedekindDomain NumberField MeasureTheory
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open LanglandsTunnell.RankinSelberg
open scoped Classical

theorem AutomorphicForm.exists_rs22GlobalIntegral_godementEisenstein_self_eq_add_div_and_mul_hasProd_rsEulerPoly_self_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂))
    (Θ : HeckeEigensystem ℚ ℂ)
    (hΘ : IsArithGenuineCuspRealizable ℚ
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
        (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v)
        (adelicBox ℚ)) Θ) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (σ₀ x : ℝ), x < 0 ∧
    ∃ (ν₀ : Measure (AdeleRing (𝓞 ℚ) ℚ)ˣ) (D : Set (AdelicGL2 (𝓞 ℚ) ℚ))
      (n : ℕ) (coef : Fin n → ℂ) (φs φs' : Fin n → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (Φs : Fin n → (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
      (Zr H : ℂ → ℂ) (c₁ c₀ : ℂ),
      ν₀.IsHaarMeasure ∧
      (∀ i : Fin n, Φs i ∈ schwartzBruhat2 ℚ) ∧
      Differentiable ℂ Zr ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∑ i : Fin n, coef i * rs22GlobalIntegral ℚ D (φs i) (φs' i)
            (godementEisenstein ℚ ν₀ 1 1 (moduleChar ℚ) (moduleChar_pos ℚ) (Φs i) (s - 1 / 2))) =
          Zr s + c₁ / (s - 1) + c₀ / s) ∧
      (∀ σ : ℝ, x < σ → AnalyticAt ℂ H (σ : ℂ)) ∧
      (c₀ = 0 ∨ H 0 = 0) ∧
      (∀ s : ℂ, σ₀ < s.re →
        HasProd (fun v : {v : HeightOneSpectrum (𝓞 ℚ) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (Θ.a v.1 / Θ.b v.1) (Θ.b v.1)⁻¹
              (Θ.a v.1) (Θ.b v.1) 0).eval (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)
          ((Zr s + c₁ / (s - 1) + c₀ / s) * H s)) := by sorry
