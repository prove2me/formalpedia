-- Prove2me | Theorems.Thm_AutomorphicForm_exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
-- name    : AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/ac68b47a-4c77-5957-afc0-31c71d7cf1df
-- title:
--   Whittaker coefficients of a Bruhat–Eisenstein family: continuation and decay
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele group $\mathbb{A}_F^\times$ obtained from the distributive Haar character of the adele ring, viewed with values in $\mathbb{R}^\times$; it is assumed positive, $\alpha(t)>0$ for all $t$. Let $\mu,\nu:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be characters that are unitary ($|\mu(x)|=|\nu(x)|=1$ for all $x$) and trivial on the principal ideles (i.e. idele class characters), and let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ that is invariant under the principal part, continuous and nontrivial. Let $\varphi:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that each $\varphi_s$ is an induced section for the pair $(\mu\,\alpha^{s+1/2},\nu\,\alpha^{-(s+1/2)})$, meaning $\varphi_s(bg)=\mu\alpha^{s+1/2}(b_{00})\,\nu\alpha^{-(s+1/2)}(b_{11})\,\varphi_s(g)$ for every $b$ in the adelic Borel subgroup (lower left entry $0$), each $\varphi_s$ is $K$-finite at every infinite place and a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup under right translation, $(s,g)\mapsto\varphi_s(g)$ is continuous, and $s\mapsto\varphi_s(g)$ is entire for each $g$. Put $E_s(h)=\varphi_s(h)+\sum_{\xi\in F}^{\prime}\varphi_s(w\,n(\xi)h)$, where $w$ is the adelic Weyl element and $n(\xi)$ the upper unipotent matrix with entry the image of $\xi$, and put $\mathrm{hgt}(b)=\alpha(b_{00})/\alpha(b_{11})$ for $b$ in the adelic Borel subgroup. The assertion is that there exists a family $\mathcal{W}_\xi(s,h)$, indexed by the nonzero $\xi\in F$, such that: (1) for all $\xi,h$ the function $s\mapsto\mathcal{W}_\xi(s,h)$ is analytic on a neighbourhood of each point of $\{\operatorname{Re}s>0\}$; (2) for $\operatorname{Re}s>1$ one has $\mathcal{W}_\xi(s,h)=\int \big(E_s\big)(n(x)h)\,\psi(-\xi x)\,d\nu(x)$, the Whittaker coefficient of $E_s$ at $\xi$ taken with respect to $\psi$ and the fixed carrier data `productionPins F` (the centre-cut Siegel set, the level-one subgroups, the Hecke generators and the adelic box); (3) for each $\xi$ the map $(s,h)\mapsto\mathcal{W}_\xi(s,h)$ is continuous on $\{\operatorname{Re}s>0\}\times\mathrm{GL}_2(\mathbb{A}_F)$; (4) for every compact $C\subseteq\{\operatorname{Re}s>0\}$ and every compact $\Omega\subseteq\mathrm{GL}_2(\mathbb{A}_F)$ there is a summable $u:F\setminus\{0\}\to\mathbb{R}$ with $\|\mathcal{W}_\xi(s,h)\|\le u(\xi)$ for all $\xi$, all $s\in C$ and all $h\in\Omega$; and (5) for every such $C$, $\Omega$, every $c'>0$ and every $N\in\mathbb{N}$ there is $M\in\mathbb{R}$ such that for $s\in C$, $b$ in the adelic Borel subgroup with $\mathrm{hgt}(b)\ge c'$ and $\omega\in\Omega$, the sum $\sum_{\xi\neq0}\|\mathcal{W}_\xi(s,b\omega)\|$ converges and is at most $M\,\mathrm{hgt}(b)^{-N}$.
--
--   This is the analytic continuation to the half plane $\operatorname{Re}s>0$, together with locally uniform summability and rapid decay in the Borel height, of the non-constant Fourier–Whittaker coefficients of the Bruhat-expanded Eisenstein family induced from unitary idele class characters $(\mu\alpha^{s+1/2},\nu\alpha^{-(s+1/2)})$; unlike the constant term, these coefficients have no poles in that region. It feeds the statement that $E_s$ minus its constant term continues analytically and decays faster than any power of the height.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary.lean

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

theorem AutomorphicForm.exists_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
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
