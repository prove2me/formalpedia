-- Prove2me | Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_diagOne_continuation_of_flat_family
-- name    : AutomorphicForm.exists_whittakerCoefficient_diagOne_continuation_of_flat_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/0430aef9-ae49-5ce8-9703-1301c26d19d2
-- title:
--   Continuation of Whittaker coefficients to Re s>0
-- statement:
--   Let $F$ be a number field and let $\alpha\colon \mathbb{A}_F^\times\to\mathbb{R}^\times$ be the modulus character, namely the `distribHaarChar` of the adele ring $\mathbb{A}_F$ pushed into $\mathbb{R}^\times$, assumed (hypothesis `hα`) to take positive real values. Let $\psi$ be an additive character of $\mathbb{A}_F$ which is trivial on all principal adeles, continuous and nontrivial, and let $\varphi\colon\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family of sections such that: for each $s$, $\varphi_s(bg)=\alpha(b_{11})^{s+1/2}\,\alpha(b_{22})^{-(s+1/2)}\varphi_s(g)$ for every upper triangular $b$ (`IsInducedSection` for `etaFst 1 α hα s` and `etaSnd 1 α hα s`); for each $s$ and each infinite place $w$, the right translates of $\varphi_s$ by the row-isometry subgroup at $w$ span a finite-dimensional space; for each $s$ the stabiliser of $\varphi_s$ under right translation by the matrices with trivial archimedean component is open; $(s,g)\mapsto\varphi_s(g)$ is continuous; $s\mapsto\varphi_s(g)$ is entire for each $g$; and the family is flat, i.e. $\varphi_s(k)=\varphi_{s'}(k)$ whenever the finite part of $k$ lies in the integral subgroup `finiteIntegralGL2` and every archimedean component of $k$ satisfies `IsRowIsometry` (determinant of norm one, rows acting isometrically on the quadratic form $\|x\|^2+\|y\|^2$). Put $E_s(h)=\varphi_s(h)+\sum_{\xi\in F}\varphi_s(w\,u(\xi)\,h)$, where $w=\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $u(\xi)=\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ are taken with entries in $F$ viewed adelically. The assertion is the existence of a function $\mathcal{J}$ assigning to each nonzero $\xi\in F$, each $s\in\mathbb{C}$ and each idele $y$ a complex number, such that: (1) for fixed $\xi,y$ the function $s\mapsto\mathcal{J}_\xi(s,y)$ is analytic on a neighbourhood of every point of $\{\operatorname{Re} s>0\}$; (2) for $\operatorname{Re} s>1$ it equals the Whittaker coefficient $\int_{\mathbb{A}_F}E_s(u(x)\,\mathrm{diag}(y,1))\,\psi(-\xi x)\,d\nu(x)$, where $\nu$ is the additive measure fixed by `productionPins F` (adelic Haar measure conditioned on the adelic box); (3) $(s,y)\mapsto\mathcal{J}_\xi(s,y)$ is continuous on $\{\operatorname{Re} s>0\}\times\mathbb{A}_F^\times$; (4) $\mathcal{J}_\xi(s,\eta y)=\mathcal{J}_{\xi\eta}(s,y)$ for $\eta\in F^\times$ and $\operatorname{Re} s>0$; and (5) for every compact $C\subseteq\{\operatorname{Re} s>0\}$ and compact $U\subseteq\mathbb{A}_F^\times$ there are $k\in\mathbb{N}$ and a fractional ideal $I$ of $F$ such that for every $N\in\mathbb{N}$ there is $c\in\mathbb{R}$ with: for all $s\in C$, $u\in U$, all $r>0$ and all ideles $z$ whose finite part is $1$ and all of whose archimedean coordinates equal $r$, and all $\xi\neq 0$, one has $\mathcal{J}_\xi(s,zu)=0$ unless $\xi\in I$, and $$\|\mathcal{J}_\xi(s,zu)\|\le c\,r^{[F:\mathbb{Q}](1/2-\operatorname{Re} s)}\max(1,|N_{F/\mathbb{Q}}\xi|)^{k}\prod_{w\ \mathrm{real}}(1+r|\xi_w|)^{-N}\prod_{w\ \mathrm{complex}}(1+r\|\xi_w\|)^{-2N},$$ the $\xi_w$ being the components of $\xi$ under the mixed embedding.
--
--   This is the analytic continuation, past the line $\operatorname{Re} s=1$ of absolute convergence, of the individual Whittaker (Fourier) coefficients of the Bruhat-form Eisenstein series attached to a flat family of induced sections on $\mathrm{GL}_2$ over a number field, together with the uniform rapid decay in $\xi$ and the power-of-$r$ growth in the archimedean dilation needed to resum them. It is used in the continuation and summability statement for the full Bruhat Eisenstein series, [`AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family`](thm.html#AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_diagOne_continuation_of_flat_family.lean

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

theorem AutomorphicForm.exists_whittakerCoefficient_diagOne_continuation_of_flat_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
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
