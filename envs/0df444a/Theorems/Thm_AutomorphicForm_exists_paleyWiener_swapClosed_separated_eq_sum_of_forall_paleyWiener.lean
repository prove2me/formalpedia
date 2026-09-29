-- Prove2me | Theorems.Thm_AutomorphicForm_exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener
-- name    : AutomorphicForm.exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/0d6feda4-4127-5a60-b6b5-d51562eec729
-- title:
--   Swap-closed separated normal form for summed Paley–Wiener data
-- statement:
--   Let $F$ be a number field and let $\alpha$ denote the homomorphism from the ideles $(\mathbb{A}_F)^\times$ to $\mathbb{R}^\times$ obtained from the distributive Haar character of the adele ring, with $\alpha(x)>0$ for all $x$ assumed as a hypothesis $h\alpha$. Fix reals $0<d_1<d_2$, a set $\Phi\subseteq \mathrm{GL}_2(\mathbb{A}_F)$, and a continuous character $\xi$ of the group $Z$ attached to `productionPinsOf` for the data $\Phi$, the levels `levelOne`, the Hecke generators `heckeGen` and the box `adelicBox` (this $Z$ is all of $(\mathbb{A}_F)^\times$), with $|\xi|\equiv 1$; fix reals $a,b$ and $n\in\mathbb{N}$. Given characters $\mu_0(j),\nu_0(j)$ of $(\mathbb{A}_F)^\times$ for $j<n$ which are unitary, trivial on the principal ideles $F^\times$, continuous, and satisfy $\mu_0(j)\nu_0(j)=\xi$ on $Z$; given families $\psi f_0(j,s,\cdot)$ each of which is a section induced from the pair $(\mu_0(j)\alpha^{\,s+1/2},\nu_0(j)\alpha^{-(s+1/2)})$, i.e. transforms under left multiplication by an upper triangular adelic matrix $b$ by the product of these characters evaluated at the diagonal entries $b_{00}$, $b_{11}$, and which is jointly continuous in $(s,g)$, entire in $s$, $K_\infty$-finite (finitely many spanning right translates under each `archRowIsometrySubgroup`), $K_f$-smooth, of uniformly bounded $K_\infty$-type at each infinite place (a fixed finite-dimensional space of functions on `archRowIsometrySubgroup` containing all right translates, uniformly in $s$ and $g$), and rapidly decreasing on vertical lines with an integrable bounded majorant, uniformly for $g$ in a compact set; and given functions $\psi_0(j)$ which are slab profiles for $Z,\xi$ (measurable, invariant under left multiplication by unipotent adelic matrices and by global rational Borel points, transforming by $\xi$ under the adelic centre, bounded on slabs, with a height band), represented on every vertical line by $\psi_0(j)(g)=(4\pi)^{-1}\int_{\mathbb{R}}\psi f_0(j,\sigma'+it,g)\,dt$ and vanishing outside the height band $\mathrm{adelicHeight}_F(g)\in[a,b]$: then there exist a finite index type $\iota$, characters $\mu_e,\nu_e$ with the same four properties and $\mu_e\nu_e=\xi$ on $Z$, a map $r:\iota\to\iota$ with $\mu_{r e}=\nu_e$ and $\nu_{r e}=\mu_e$, pairwise separation on the norm-one ideles (for $e\neq e'$ some $x$ in the kernel of the distributive Haar character with $\mu_e x\neq\mu_{e'}x$ or $\nu_e x\neq\nu_{e'}x$), section families $\psi f_e$ with all the listed induction, continuity, holomorphy, $K_\infty$-finiteness, $K_f$-smoothness, uniform $K_\infty$-type and decay properties, and a function $\psi$ which is a slab profile for $Z,\xi$, satisfies $\psi(g)=\sum_e (4\pi)^{-1}\int_{\mathbb{R}}\psi f_e(\sigma'+it,g)\,dt$ for every $\sigma'$ and $g$, vanishes outside the band $[a,b]$, and equals the pointwise sum $\sum_j \psi_0(j)$.
--
--   This is the normalisation step which puts a finite collection of one-index Paley–Wiener data for $\mathrm{GL}_2$ over a number field into the shape required by the Parseval identity on the unitary axis: the pairs of characters are made pairwise distinct already on the norm-one ideles and the family is closed under the exact swap of the two inducing characters, while the profile is unchanged, being the sum of the given ones. It feeds the density statement for Paley–Wiener slab profiles in $L^p$ on the rational torus–unipotent quotient, whose datum block it produces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
      (_hξ : Continuous ξ) (_hξu : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
      (a b : ℝ)
      (n : ℕ) (μ₀ ν₀ : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ₀ : ∀ j, IsUnitaryChar (𝓞 F) F (μ₀ j)) (_hν₀ : ∀ j, IsUnitaryChar (𝓞 F) F (ν₀ j))
      (_hμ₀ic : ∀ j, IsIdeleClassChar (𝓞 F) F (μ₀ j)) (_hν₀ic : ∀ j, IsIdeleClassChar (𝓞 F) F (ν₀ j))
      (_hμ₀c : ∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ₀ j x : ℂˣ) : ℂ))
      (_hν₀c : ∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν₀ j x : ℂˣ) : ℂ))
      (_hμ₀ν₀ : ∀ (j : Fin n) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ₀ j (z : (AdeleRing (𝓞 F) F)ˣ) * ν₀ j (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z)
      (ψf₀ : Fin n → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf₀ : ∀ j s, IsInducedSection (𝓞 F) F (etaFst (μ₀ j) α hα s) (etaSnd (ν₀ j) α hα s) (ψf₀ j s))
      (_hψ₀jc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf₀ j p.1 p.2))
      (_hψ₀hol : ∀ j g, Differentiable ℂ (fun s => ψf₀ j s g))
      (_hψ₀K : ∀ j s, IsArchKFinite F (ψf₀ j s)) (_hψ₀sm : ∀ j s, IsKfSmooth F (ψf₀ j s))
      (_hψ₀Ku : ∀ (j : Fin n) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf₀ j s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hψ₀dec : ∀ (j : Fin n) (m₀ : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ m₀ * ‖ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₀ : Fin n → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ₀ : ∀ j, AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ (ψ₀ j))
      (_hψ₀rep : ∀ (j : Fin n) (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ₀ j g = (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψ₀band : ∀ (j : Fin n) (g : AdelicGL2 (𝓞 F) F), ψ₀ j g ≠ 0 →
        NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b),
    ∃ (ι : Type) (_ : Fintype ι) (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (r : ι → ι)
      (ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ) (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ e, IsUnitaryChar (𝓞 F) F (μ e)) ∧ (∀ e, IsUnitaryChar (𝓞 F) F (ν e)) ∧
      (∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) ∧ (∀ e, IsIdeleClassChar (𝓞 F) F (ν e)) ∧
      (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ)) ∧
      (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ)) ∧
      (∀ (e : ι) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ e (z : (AdeleRing (𝓞 F) F)ˣ) * ν e (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z) ∧
      (∀ e, μ (r e) = ν e ∧ ν (r e) = μ e) ∧
      (∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x) ∧
      (∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s)) ∧
      (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2)) ∧
      (∀ e g, Differentiable ℂ (fun s => ψf e s g)) ∧
      (∀ e s, IsArchKFinite F (ψf e s)) ∧ (∀ e s, IsKfSmooth F (ψf e s)) ∧
      (∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) ∧
      (∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) ∧
      AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ ∧
      (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, ψ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b) ∧
      (ψ = fun g => ∑ j, ψ₀ j g) := by sorry
