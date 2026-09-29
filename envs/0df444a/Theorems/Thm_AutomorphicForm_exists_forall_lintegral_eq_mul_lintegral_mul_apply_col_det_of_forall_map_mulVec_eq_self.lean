-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_eq_mul_lintegral_mul_apply_col_det_of_forall_map_mulVec_eq_self
-- name    : AutomorphicForm.exists_forall_lintegral_eq_mul_lintegral_mul_apply_col_det_of_forall_map_mulVec_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/cab15747-e6b8-5a11-859d-aca70230b612
-- title:
--   Uniqueness of the invariant measure on the orbit of (e₁,1)
-- statement:
--   Let $K$ be a number field, $\mathbb{A}=\mathbb{A}_K$ its adele ring, with $\mathbb{A}$ and its unit group $\mathbb{A}^\times$ carrying their Borel $\sigma$-algebras, and with $G=\mathrm{GL}_2(\mathbb{A})$ carrying the Borel $\sigma$-algebra of its topology (the local instance `glBorel`). Assume given: a Haar measure $\tau$ on $G$; an additive Haar measure $\mu$ on $\mathbb{A}$; a measurable function $w\colon G\to[0,\infty]$ such that for every $g\in G$ one has $\int_{\mathbb{A}} w\bigl(g\cdot \begin{pmatrix}1&x\\0&1\end{pmatrix}\bigr)\,d\mu(x)=1$, where the matrix is [`AutomorphicForm.unipotentGL2 x`](def/AutomorphicForm_ConstantTerm.html#L17); and a $\sigma$-finite measure $\rho$ on $\mathbb{A}^2\times\mathbb{A}^\times$ (the product $(\mathrm{Fin}\,2\to\mathbb{A})\times\mathbb{A}^\times$) such that, first, for every $h\in G$ the pushforward of $\rho$ along $(c,\delta)\mapsto (h\,c,\ \det(h)\,\delta)$ equals $\rho$, and, second, the set of pairs $(c,\delta)$ that are not of the form $\bigl((g_{i0})_i,\det g\bigr)$ for some $g\in G$ is $\rho$-null. The conclusion is that there exists $c\in[0,\infty]$ with $c\neq\infty$ such that for every measurable $\Psi\colon \mathbb{A}^2\times\mathbb{A}^\times\to[0,\infty]$,
--   $$\int \Psi\,d\rho \;=\; c\int_G w(g)\,\Psi\bigl((g_{i0})_i,\det g\bigr)\,d\tau(g).$$
--
--   This is the uniqueness, up to a finite scalar factor, of a $\mathrm{GL}_2(\mathbb{A})$-invariant $\sigma$-finite measure carried by the orbit of $(e_1,1)$ in $\mathbb{A}^2\times\mathbb{A}^\times$, i.e. on $G/N$ with $N$ the upper unipotent subgroup, expressed inside the ambient space via the map $g\mapsto(ge_1,\det g)$ and with the transverse normalisation supplied by $w$. It is used in the analysis of constant terms of automorphic forms on $\mathrm{GL}_2$ over $K$, feeding into the identification of such an invariant integral with an iterated integral involving the idele norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_eq_mul_lintegral_mul_apply_col_det_of_forall_map_mulVec_eq_self.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_lintegral_eq_mul_lintegral_mul_apply_col_det_of_forall_map_mulVec_eq_self
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (τ : Measure (GL (Fin 2) (AdeleRing (𝓞 K) K))) (hτ : τ.IsHaarMeasure)
    (μ : Measure (AdeleRing (𝓞 K) K)) (hμ : μ.IsAddHaarMeasure)
    (w : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℝ≥0∞) (hw : Measurable w)
    (hw1 : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K), ∫⁻ x, w (g * AutomorphicForm.unipotentGL2 x) ∂μ = 1)
    (ρ : Measure ((Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ)) (hρ : SigmaFinite ρ)
    (hρinv : ∀ h : GL (Fin 2) (AdeleRing (𝓞 K) K),
      Measure.map (fun p : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ =>
        ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).mulVec p.1,
          Matrix.GeneralLinearGroup.det h * p.2)) ρ = ρ)
    (hρ0 : ρ {p | ¬ ∃ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      ((fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0),
        Matrix.GeneralLinearGroup.det g) = p} = 0) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧
      ∀ Ψ : (Fin 2 → AdeleRing (𝓞 K) K) × (AdeleRing (𝓞 K) K)ˣ → ℝ≥0∞, Measurable Ψ →
        ∫⁻ p, Ψ p ∂ρ =
          c * ∫⁻ g, w g * Ψ (fun i => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i 0,
            Matrix.GeneralLinearGroup.det g) ∂τ := by sorry
