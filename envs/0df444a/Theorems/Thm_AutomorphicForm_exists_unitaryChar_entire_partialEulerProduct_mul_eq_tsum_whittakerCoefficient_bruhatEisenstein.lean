-- Prove2me | Theorems.Thm_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein
-- name    : AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/7bbe5f05-60f4-5b31-b4eb-3de75aaa7a9b
-- title:
--   Euler product for Whittaker sums of GL₂ Eisenstein families
-- statement:
--   Let $F$ be a number field, $\mathbb{A}_F$ its adele ring, and let $\alpha\colon\mathbb{A}_F^\times\to\mathbb{R}^\times$ be the character obtained from the distributive Haar character of $\mathbb{A}_F$ composed with $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passed to units; assume $\alpha$ takes positive values and satisfies $\alpha(u)=1$ for every $u\in F^\times$ embedded in the ideles. Let $\mu,\nu\colon\mathbb{A}_F^\times\to\mathbb{C}^\times$ be characters with $\|\mu(x)\|=\|\nu(x)\|=1$ for all ideles $x$ and $\mu(u)=\nu(u)=1$ for all $u\in F^\times$, and let $\psi$ be an additive character of $\mathbb{A}_F$ into $\mathbb{C}$ that is continuous, non-trivial and invariant under the principal part (i.e. `IsGlobalAddChar`). Let $\varphi\colon\mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be such that for every $s$, $\varphi_s(bg)=\mu\alpha^{s+1/2}(b_1)\,\nu\alpha^{-(s+1/2)}(b_2)\,\varphi_s(g)$ for $b$ in the adelic Borel with diagonal entries $b_1,b_2$, $\varphi_s$ is archimedean $K$-finite at every infinite place and a smooth vector for the finite adelic $\mathrm{GL}_2$-subgroup under right translation, with $(s,g)\mapsto\varphi_s(g)$ jointly continuous and $s\mapsto\varphi_s(g)$ entire for each $g$. Fix $g\in\mathrm{GL}_2(\mathbb{A}_F)$. Then there exist a continuous character $\chi\colon\mathbb{A}_F^\times\to\mathbb{C}^\times$ with $\|\chi(x)\|=1$ and $\chi|_{F^\times}=1$, a finite set $S$ of height-one primes of $\mathcal{O}_F$, local units $\varpi_v$ of valuation $\mathrm{ofAdd}(-1)$ at every $v$, and an entire $N_c\colon\mathbb{C}\to\mathbb{C}$, such that for all $s$ with $\operatorname{Re} s>1$,
--   $$\Bigl(\prod_{v\notin S}\bigl(1-\chi_v(\varpi_v)\,|\mathrm{N}v|^{-(2s+1)}\bigr)\Bigr)N_c(s)=\sum_{\xi\in F,\ \xi\neq 0}W_\psi\bigl(E(\varphi_s)\bigr)(\xi,g),$$
--   where $\chi_v$ is the local component of $\chi$ at $v$, $\mathrm{N}v$ the absolute norm of the prime, $E(\varphi_s)(g')=\varphi_s(g')+\sum_{\xi'\in F}\varphi_s(w\,n(\xi')\,g')$ with $w$ the image of the Weyl element and $n(x)$ the upper unipotent matrix, and $W_\psi(\Phi)(\xi,g)=\int\Phi(n(x)g)\,\psi(-\xi x)$ against the measure attached to `productionPins F`. No relation between $\chi$ and $\mu,\nu$ is asserted.
--
--   This is the Euler-product form of the non-constant (Bruhat) part of the Fourier–Whittaker expansion of a holomorphic family of $\mathrm{GL}_2$ Eisenstein sections: the sum of the non-zero Whittaker coefficients is an inverse partial Hecke Euler product away from a finite set of primes, times a function entire in $s$. It is the analytic input used by the statement producing the continuation of the Bruhat Eisenstein series and its limiting behaviour at $s=1/2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField IsDedekindDomain
open scoped NNReal
set_option autoImplicit false

theorem AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (_hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (g : AdelicGL2 (𝓞 F) F),
    ∃ χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ,
      Continuous χ ∧ IsUnitaryChar (𝓞 F) F χ ∧ IsIdeleClassChar (𝓞 F) F χ ∧
      ∃ (S : Finset (HeightOneSpectrum (𝓞 F)))
        (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
        (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) ∧
        ∃ Nc : ℂ → ℂ, Differentiable ℂ Nc ∧
          ∀ s : ℂ, 1 < s.re →
            (∏' v : {v // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * Nc s =
            ∑' ξ : {ξ : F // ξ ≠ 0},
              whittakerCoefficient F (productionPins F) ψ
                (fun g' => φ s g' + ∑' ξ' : F, φ s (adelicWeyl (𝓞 F) F
                    * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) (ξ : F) g := by sorry
