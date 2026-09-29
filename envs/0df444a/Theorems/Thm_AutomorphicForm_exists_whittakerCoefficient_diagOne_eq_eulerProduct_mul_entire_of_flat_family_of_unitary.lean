-- Prove2me | Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_of_flat_family_of_unitary
-- name    : AutomorphicForm.exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_of_flat_family_of_unitary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/09b709d4-2d2c-52b9-b063-fc1e424375b1
-- title:
--   Euler block times entire remainder in flat GL₂ Whittaker coefficients
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the idelic modulus, i.e. the character of the idele group $\mathbb{A}_F^\times$ obtained from the distributive Haar character of the adele ring, assumed everywhere positive. Fix characters $\mu,\nu:\mathbb{A}_F^\times\to\mathbb{C}^\times$ that are unitary ($|\chi(x)|=1$ for all $x$) and trivial on the principal ideles $F^\times$; an additive character $\psi$ of $\mathbb{A}_F$ that is trivial on $F$, continuous and nontrivial; and a family $\varphi:\mathbb{C}\times \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that each $\varphi_s$ satisfies $\varphi_s(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi_s(g)$ for upper-triangular $b$, with $\eta_1=\mu\alpha^{s+1/2}$ and $\eta_2=\nu\alpha^{-(s+1/2)}$; such that the right translates of $\varphi_s$ under the row-isometry subgroup at each infinite place span a finite-dimensional space; the stabiliser of $\varphi_s$ in the subgroup of elements with trivial archimedean part is open; $(s,g)\mapsto\varphi_s(g)$ is continuous; $s\mapsto\varphi_s(g)$ is entire; and the family is flat, $\varphi_s(k)=\varphi_{s'}(k)$ whenever $k$ has integral finite part and all archimedean components are row isometries. Fix also uniformisers $\varpi_v$ of each completion, of valuation $\mathrm{ofAdd}(-1)$, and set $E_s(h)=\varphi_s(h)+\sum_{\xi\in F}\varphi_s(w\,u(\xi)h)$, with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix. Then there is a family $\mathcal{J}_\xi(s,y)$, indexed by $\xi\in F\setminus\{0\}$ and defined for $s\in\mathbb{C}$, $y\in\mathbb{A}_F^\times$, with: (i) $s\mapsto\mathcal{J}_\xi(s,y)$ analytic on a neighbourhood of each point of $\mathbb{C}$; (ii) a finite set $S$ of finite places such that for $\mathrm{Re}\,s>1$ the $\xi$-th Whittaker coefficient of $E_s$ against $\psi$ at $\mathrm{diag}(y,1)$, formed with the measure pinned by `productionPins F` (the adelic additive Haar measure conditioned on the adelic box), equals $\prod_{v\notin S}\bigl(1-(\mu\nu^{-1})_v(\varpi_v)N(v)^{-(2s+1)}\bigr)\cdot\mathcal{J}_\xi(s,y)$, where $(\mu\nu^{-1})_v$ is the local component of $\mu\nu^{-1}$ and $N(v)$ the absolute norm of $v$; (iii) $(s,y)\mapsto\mathcal{J}_\xi(s,y)$ continuous; (iv) $\mathcal{J}_\xi(s,\eta y)=\mathcal{J}_{\xi\eta}(s,y)$ for $\eta\in F^\times$; and (v) for all compact $C\subseteq\mathbb{C}$, compact $U\subseteq\mathbb{A}_F^\times$ and $r_0>0$ there are $k\in\mathbb{N}$ and a fractional ideal $I$ of $F$ such that for every $N\in\mathbb{N}$ there is $c$ with: for $s\in C$, $u\in U$, every idele $z$ with trivial finite part whose archimedean components are all equal to the real number $r\ge r_0$, and every $\xi\neq 0$, one has $\mathcal{J}_\xi(s,zu)=0$ unless $\xi\in I$, and $\|\mathcal{J}_\xi(s,zu)\|\le c\,r^{[F:\mathbb{Q}](1/2-\mathrm{Re}\,s)}\max(1,|N_{F/\mathbb{Q}}\xi|)^k\prod_{w\ \mathrm{real}}(1+r|\xi_w|)^{-N}\prod_{w\ \mathrm{complex}}(1+r\|\xi_w\|)^{-2N}$, the $\xi_w$ being the components of $\xi$ under the mixed embedding.
--
--   This is the torus-restricted Whittaker expansion of the Bruhat-form Eisenstein series attached to a flat family of induced sections, in the shape 'inverse partial Hecke $L$-factor at $2s+1$ for $\mu\nu^{-1}$ times an entire remainder', the remainder carrying rapid decay in $\xi$ and the expected $r^{[F:\mathbb{Q}](1/2-\mathrm{Re}\,s)}$ growth under archimedean dilation. It is the version with the Euler block divided out, and it feeds the summable Fourier-expansion statement [`AutomorphicForm.exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary`](thm.html#AutomorphicForm.exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_of_flat_family_of_unitary.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.InfinitePlace
open AutomorphicForm
open AutomorphicForm.WindowedSiegel Filter Topology IsDedekindDomain
open scoped NNReal

open scoped Classical in

theorem AutomorphicForm.exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_of_flat_family_of_unitary
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
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
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    ∃ 𝒥 : {ξ : F // ξ ≠ 0} → ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ,
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ),
        AnalyticOnNhd ℂ (fun s => 𝒥 ξ s y) Set.univ) ∧
      (∃ S : Finset (HeightOneSpectrum (𝓞 F)),
        ∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ), 1 < s.re →
          whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) (diagOne y)
            = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                  * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * 𝒥 ξ s y) ∧
      (∀ ξ : {ξ : F // ξ ≠ 0}, Continuous (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => 𝒥 ξ p.1 p.2)) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ),
        𝒥 ξ s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
          = 𝒥 ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ s y) ∧
      (∀ (C : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ) (r₀ : ℝ), IsCompact C → IsCompact U → 0 < r₀ →
        ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), ∀ N : ℕ, ∃ c : ℝ,
          ∀ s ∈ C, ∀ u ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), r₀ ≤ r →
            (z : AdeleRing (𝓞 F) F).2 = 1 →
            (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
            ∀ ξ : {ξ : F // ξ ≠ 0},
              ((ξ : F) ∉ I → 𝒥 ξ s (z * u) = 0) ∧
              ‖𝒥 ξ s (z * u)‖ ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
                (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
                ∏ w : {w : InfinitePlace F // w.IsComplex},
                  (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ))) := by sorry
