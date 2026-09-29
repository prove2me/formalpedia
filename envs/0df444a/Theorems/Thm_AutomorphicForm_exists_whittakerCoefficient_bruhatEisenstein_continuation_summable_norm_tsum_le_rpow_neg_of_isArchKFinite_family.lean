-- Prove2me | Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/83fd9a16-638b-5dcf-95ce-c9f37d0f890f
-- title:
--   Continuation and decay of Bruhat–Eisenstein Whittaker coefficients
-- statement:
--   Let $F$ be a number field and let $\alpha \colon (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the unit-group character induced by the module (distributive Haar) character of the adele ring, assumed everywhere positive. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is principal-invariant, continuous and nontrivial, and let $\varphi \colon \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family such that each $\varphi_s$ satisfies $\varphi_s(bg) = \alpha(b_{00})^{s+1/2}\,\alpha(b_{11})^{-(s+1/2)}\varphi_s(g)$ for $b$ upper triangular (the induced-section condition for the characters `etaFst 1 α hα s`, `etaSnd 1 α hα s`), is archimedean $K$-finite (at every infinite place the right translates under the row-isometry subgroup span a finite-dimensional space) and $K_f$-smooth, with $(s,g) \mapsto \varphi_s(g)$ continuous and $s \mapsto \varphi_s(g)$ entire. Put $E_s(h) = \varphi_s(h) + \sum'_{\xi \in F} \varphi_s(w\, n(\xi) h)$, with $w$ the adelic Weyl element and $n(\xi)$ the upper unipotent matrix, and $\mathrm{hgt}(b) = \alpha(b_{00})/\alpha(b_{11})$ for $b$ in the adelic Borel subgroup. Then there exists $\mathcal{W}$, indexed by the nonzero $\xi \in F$, such that: (1) $s \mapsto \mathcal{W}_\xi(s,h)$ is analytic on a neighbourhood of every point of $\{\operatorname{Re} s > 0\}$; (2) for $\operatorname{Re} s > 1$ it equals the Whittaker coefficient $\int E_s(n(x)h)\,\psi(-\xi x)$ of $E_s$ at $\xi$, taken with respect to the measure of `productionPins F`; (3) $(s,h) \mapsto \mathcal{W}_\xi(s,h)$ is continuous on $\{\operatorname{Re} s > 0\} \times \mathrm{GL}_2(\mathbb{A}_F)$; (4) for all compact $C \subseteq \{\operatorname{Re} s > 0\}$ and compact $\Omega$ there is a summable $u$ on the nonzero $\xi$ with $\|\mathcal{W}_\xi(s,h)\| \le u(\xi)$ for $s \in C$, $h \in \Omega$; and (5) for all such $C$, $\Omega$, all $c' > 0$ and all $N \in \mathbb{N}$ there is $M \in \mathbb{R}$ with $\sum_{\xi \ne 0} \|\mathcal{W}_\xi(s, b\omega)\|$ summable and at most $M \cdot \mathrm{hgt}(b)^{-N}$ whenever $s \in C$, $\omega \in \Omega$ and $\mathrm{hgt}(b) \ge c'$.
--
--   This is the analytic continuation, past the region of absolute convergence, of the individual Fourier–Whittaker coefficients of the Bruhat-type Eisenstein family attached to a flat family of induced sections, together with uniform summability over the nonzero Fourier frequencies and rapid decay in the height of the Borel variable. It is used to build the non-constant term $\sum_{\xi \ne 0} \mathcal{W}_\xi$ and to establish its analyticity and moderate-growth bound, in [`AutomorphicForm.exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family`](thm.html#AutomorphicForm.exists_analyticOnNhd_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm Filter Topology
open scoped NNReal

theorem AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family
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
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∃ 𝒲 : {ξ : F // ξ ≠ 0} → ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (h : AdelicGL2 (𝓞 F) F),
        AnalyticOnNhd ℂ (fun s => 𝒲 ξ s h) {s : ℂ | 0 < s.re}) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 < s.re →
        𝒲 ξ s h = whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) h) ∧
      (∀ ξ : {ξ : F // ξ ≠ 0}, ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => 𝒲 ξ p.1 p.2)
        ({s : ℂ | 0 < s.re} ×ˢ Set.univ)) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)), IsCompact C → C ⊆ {s : ℂ | 0 < s.re} → IsCompact Ω →
        ∃ u : {ξ : F // ξ ≠ 0} → ℝ, Summable u ∧
          ∀ (ξ : {ξ : F // ξ ≠ 0}), ∀ s ∈ C, ∀ h ∈ Ω, ‖𝒲 ξ s h‖ ≤ u ξ) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
        IsCompact C → C ⊆ {s : ℂ | 0 < s.re} → IsCompact Ω → 0 < c' →
        ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
          ω ∈ Ω → c' ≤ hgt b →
            Summable (fun ξ : {ξ : F // ξ ≠ 0} => ‖𝒲 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖) ∧
            ∑' ξ : {ξ : F // ξ ≠ 0}, ‖𝒲 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤ M * (hgt b) ^ (-(N : ℝ))) := by sorry
