-- Prove2me | Theorems.Thm_AutomorphicForm_exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family
-- name    : AutomorphicForm.exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/d8cfcbeb-49c9-5e16-bd2a-14b19b41c03a
-- title:
--   Flat K-finite induced sections as L^S times Godement sections
-- statement:
--   Let $F$ be a number field, equip the idele group $(\mathbb{A}_F)^\times$ with a measurable/Borel structure and fix a Haar measure $\nu_0$ on it, and let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the unit-group-valued character obtained from the distributive Haar character `distribHaarChar` of $\mathbb{A}_F$ by the coercion $\mathbb{R}_{\ge 0}\to\mathbb{R}$, assumed to take strictly positive values (hypothesis `hα`). Let $\mu,\nu : (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be characters with $|\mu(x)|=|\nu(x)|=1$ for all $x$ and with continuous underlying $\mathbb{C}$-valued functions, and let $\psi : \mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that: for every $s$, $\psi_s(bg)=\eta_1(\mathrm{diag}_1 b)\,\eta_2(\mathrm{diag}_2 b)\,\psi_s(g)$ for all $b$ in the adelic Borel subgroup and all $g$, where $\eta_1=\mu\cdot\alpha^{s+1/2}$ and $\eta_2=\nu\cdot\alpha^{-(s+1/2)}$ in the sense of `etaFst`, `etaSnd`; for every $s$ and every infinite place $w$ the right translates of $\psi_s$ under the row-isometry subgroup at $w$ span a finite-dimensional space, and $\psi_s$ is a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup; $(s,g)\mapsto\psi_s(g)$ is jointly continuous; $s\mapsto\psi_s(g)$ is differentiable for each $g$; and the family is flat, i.e. $\psi_s(k)=\psi_{s'}(k)$ whenever the finite part of $k$ lies in `finiteIntegralGL2` and each archimedean component of $k$ is a row isometry (determinant of norm $1$ and preservation of the sum of squared norms of the two coordinates). The conclusion asserts the existence of $n\in\mathbb{N}$, functions $\Phi_1,\dots,\Phi_n$ on $\mathbb{A}_F^2$ lying in `schwartzBruhat2` (the span of pure tensors), entire functions $B_1,\dots,B_n$ on $\mathbb{C}$, a finite set $S$ of finite places, and uniformisers $\varpi_v$ at every finite place (valuation equal to $\mathrm{ofAdd}(-1)$), such that for all $s$ with $\operatorname{Re} s>0$ and all $g\in\mathrm{GL}_2(\mathbb{A}_F)$, $$\sum_{i} B_i(s)\, f_{\Phi_i}(s,g) = \Bigl(\prod_{v\notin S}\bigl(1-\chi_v(\varpi_v)\,N(v)^{-(2s+1)}\bigr)^{-1}\Bigr)\,\psi_s(g),$$ where $\chi=\mu\nu^{-1}$, $\chi_v$ is its local component `localChar`, $N(v)$ is the absolute norm of $v$, the product is the unconditional product over the places outside $S$, and $f_\Phi(s,g)$ is the Godement section $\mu(\det g)\,\alpha(\det g)^{s+1/2}$ times Tate's global zeta integral (with respect to $\nu_0$) of $t\mapsto \Phi$ of the bottom row vector of $g$ scaled by $t$, at the character $\mu\nu^{-1}$ and exponent $2s+1$.
--
--   This is the statement that Godement's standard sections, built from Schwartz–Bruhat functions on $\mathbb{A}_F^2$, generate the $K$-finite part of the principal series induced from a pair of unitary idele characters, in the normalisation where the spherical Godement section equals the partial $L$-factor $L^S(2s+1,\mu\nu^{-1})$ times the flat spherical section. It is used in establishing the analytic continuation of the Weyl intertwining integral for $K$-finite families of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.exists_sum_mul_godementSection_eq_partialEulerProduct_mul_of_flat_family
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      (_hψK : ∀ s, IsArchKFinite F (ψ s))
      (_hψf : ∀ s, IsKfSmooth F (ψ s))
      (_hψjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2))
      (_hψhol : ∀ g, Differentiable ℂ (fun s => ψ s g))
      (_hψflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ s k = ψ s' k),
    ∃ (n : ℕ) (Φ : Fin n → (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (B : Fin n → ℂ → ℂ)
      (S : Finset (HeightOneSpectrum (𝓞 F)))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
      (∀ i, Φ i ∈ schwartzBruhat2 F) ∧
      (∀ i, Differentiable ℂ (B i)) ∧
      (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
      ∀ s : ℂ, 0 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        (∑ i, B i s * godementSection F ν₀ μ ν α hα (Φ i) s g)
          = (∏' v : {v // v ∉ S},
              (1 - ((localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹)
            * ψ s g := by sorry
