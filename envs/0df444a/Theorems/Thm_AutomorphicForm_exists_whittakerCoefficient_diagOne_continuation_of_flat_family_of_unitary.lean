-- Prove2me | Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary
-- name    : AutomorphicForm.exists_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/6aa1b0af-40c3-5a37-83b8-f8aff6c25fb7
-- title:
--   Continuation of Whittaker coefficients of a unitary flat Eisenstein family
-- statement:
--   Let $F$ be a number field, and let $\alpha$ be the character of the idele group $\mathbb{A}_F^\times$ obtained from the module `distribHaarChar` of the adele ring, valued in $\mathbb{R}^\times$, with $\alpha$ assumed pointwise positive. Let $\mu,\nu:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be characters that are unitary ($|\chi(x)|=1$ for every idele) and trivial on the principal ideles coming from $F^\times$, and let $\psi$ be an additive character of $\mathbb{A}_F$ that is trivial on $F$, continuous and nontrivial. Let $\varphi:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy: for each $s$, $\varphi_s(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi_s(g)$ for $b$ in the adelic Borel subgroup (lower-left entry zero), where $\eta_1=\mu\cdot\alpha^{s+1/2}$ and $\eta_2=\nu\cdot\alpha^{-(s+1/2)}$; at each infinite place $w$ the right translates of $\varphi_s$ under the group of row isometries at $w$ span a finite-dimensional space; the stabiliser of $\varphi_s$ under right translation by the kernel of the archimedean projection (the finite-adelic subgroup) is open; $(s,g)\mapsto\varphi(s,g)$ is continuous; $s\mapsto\varphi_s(g)$ is entire; and $\varphi$ is flat, i.e. $\varphi_s(k)=\varphi_{s'}(k)$ whenever the finite part of $k$ lies in $\mathrm{GL}_2$ of the integral finite adeles and every archimedean component of $k$ is a row isometry. Put $E_s(h)=\varphi_s(h)+\sum_{\xi\in F}\varphi_s(w\,u(\xi)h)$, with $w$ the adelic Weyl element and $u(\xi)$ the upper unipotent matrix. The assertion is that there exists $\mathcal{J}$, assigning to each $\xi\in F\setminus\{0\}$, each $s\in\mathbb{C}$ and each idele $y$ a complex number, such that: (1) for fixed $\xi,y$ the function $s\mapsto\mathcal{J}_\xi(s,y)$ is analytic on a neighbourhood of each point of $\{\operatorname{Re}s>0\}$; (2) for $\operatorname{Re}s>1$ it equals the $\xi$-th Whittaker coefficient $\int E_s(u(x)\,\mathrm{diag}(y,1))\,\psi(-\xi x)$, taken with respect to the measure of `productionPins`; (3) $(s,y)\mapsto\mathcal{J}_\xi(s,y)$ is continuous on $\{\operatorname{Re}s>0\}$ times the whole idele group; (4) $\mathcal{J}_\xi(s,\eta y)=\mathcal{J}_{\xi\eta}(s,y)$ for $\eta\in F^\times$ and $\operatorname{Re}s>0$; and (5) for every compact $C\subseteq\{\operatorname{Re}s>0\}$ and every compact set $U$ of ideles there are $k\in\mathbb{N}$ and a fractional ideal $I$ of $F$ such that for every $N\in\mathbb{N}$ there is $c\in\mathbb{R}$ with the following property: for all $s\in C$, $u\in U$, every idele $z$ whose finite part is $1$ and all of whose archimedean components equal a real $r>0$, and every $\xi\neq 0$, one has $\mathcal{J}_\xi(s,zu)=0$ unless $\xi\in I$, and $$\|\mathcal{J}_\xi(s,zu)\|\le c\,r^{[F:\mathbb{Q}](1/2-\operatorname{Re}s)}\max(1,|N_{F/\mathbb{Q}}(\xi)|)^{k}\prod_{w\ \mathrm{real}}(1+r|\xi_w|)^{-N}\prod_{w\ \mathrm{complex}}(1+r\|\xi_w\|)^{-2N},$$ the components $\xi_w$ being those of the mixed embedding of $\xi$.
--
--   This is the analytic continuation, from $\operatorname{Re}s>1$ to the half-plane $\operatorname{Re}s>0$, of the non-degenerate Fourier–Whittaker coefficients along the torus $\mathrm{diag}(y,1)$ of the Bruhat-form Eisenstein series attached to a flat family of sections induced from unitary idele class characters, together with the $F^\times$-equivariance in $(\xi,y)$ and uniform bounds of rapid decay in $\xi$ and controlled growth in the torus parameter $r$. It feeds the summability statement [`AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary`](thm.html#AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary), where the coefficients are summed over $\xi$ to control the continued Eisenstein series itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.InfinitePlace AutomorphicForm
open AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

open scoped Classical in

theorem AutomorphicForm.exists_whittakerCoefficient_diagOne_continuation_of_flat_family_of_unitary
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
          φ s k = φ s' k),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    ∃ 𝒥 : {ξ : F // ξ ≠ 0} → ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ,
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (y : (AdeleRing (𝓞 F) F)ˣ),
        AnalyticOnNhd ℂ (fun s => 𝒥 ξ s y) {s : ℂ | 0 < s.re}) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ), 1 < s.re →
        𝒥 ξ s y = whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) (diagOne y)) ∧
      (∀ ξ : {ξ : F // ξ ≠ 0}, ContinuousOn (fun p : ℂ × (AdeleRing (𝓞 F) F)ˣ => 𝒥 ξ p.1 p.2)
        ({s : ℂ | 0 < s.re} ×ˢ Set.univ)) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (η : Fˣ) (s : ℂ) (y : (AdeleRing (𝓞 F) F)ˣ), 0 < s.re →
        𝒥 ξ s (Units.map (algebraMap F (AdeleRing (𝓞 F) F)) η * y)
          = 𝒥 ⟨(ξ : F) * η, mul_ne_zero ξ.2 η.ne_zero⟩ s y) ∧
      (∀ (C : Set ℂ) (U : Set (AdeleRing (𝓞 F) F)ˣ), IsCompact C → C ⊆ {s : ℂ | 0 < s.re} →
        IsCompact U →
        ∃ (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), ∀ N : ℕ, ∃ c : ℝ,
          ∀ s ∈ C, ∀ u ∈ U, ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (r : ℝ), 0 < r →
            (z : AdeleRing (𝓞 F) F).2 = 1 →
            (∀ w : InfinitePlace F, Completion.extensionEmbedding w ((z : AdeleRing (𝓞 F) F).1 w) = (r : ℂ)) →
            ∀ ξ : {ξ : F // ξ ≠ 0},
              ((ξ : F) ∉ I → 𝒥 ξ s (z * u) = 0) ∧
              ‖𝒥 ξ s (z * u)‖ ≤ c * r ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) *
                (max 1 ((|Algebra.norm ℚ (ξ : F)| : ℚ) : ℝ)) ^ k *
                (∏ w : {w : InfinitePlace F // w.IsReal}, (1 + r * |(mixedEmbedding F (ξ : F)).1 w|) ^ (-(N : ℝ))) *
                ∏ w : {w : InfinitePlace F // w.IsComplex},
                  (1 + r * ‖(mixedEmbedding F (ξ : F)).2 w‖) ^ (-(2 * N : ℝ))) := by sorry
