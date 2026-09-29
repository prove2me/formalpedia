-- Prove2me | Theorems.Thm_AutomorphicForm_exists_prod_eq_and_coupled_of_coupled_prod
-- name    : AutomorphicForm.exists_prod_eq_and_coupled_of_coupled_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/40172eef-7aad-509e-ae53-fef751e936ce
-- title:
--   Coupled Haar measures on a product split factorwise
-- statement:
--   Let $G_1,G_2,H_1,H_2$ be second countable, locally compact Hausdorff topological groups, let $\varphi_i\colon G_i\to H_i$ be group homomorphisms that are closed embeddings, and let $\eta_i\colon H_i\to H_i$ be continuous endomorphisms. Fix $\gamma_i\in G_i$ and $\delta_i,y_i\in H_i$. Write $C_i=\mathrm{Cent}_{G_i}(\{\gamma_i\})$, $C=\mathrm{Cent}_{G_1\times G_2}(\{(\gamma_1,\gamma_2)\})$, and let [`AutomorphicForm.sigmaCentralizer`](def/AutomorphicForm_SigmaCentralizer.html#L10) $\eta\,\delta$ denote the subgroup $\{t: t\delta(\eta t)^{-1}=\delta\}$; put $T_i=\,$`sigmaCentralizer` $\eta_i\,\delta_i$ and $T=\,$`sigmaCentralizer` $(\eta_1\times\eta_2)\,(\delta_1,\delta_2)$. Assume given maps $e_C\colon C_1\times C_2\to C$ and $e_T\colon T_1\times T_2\to T$ whose underlying elements are formed componentwise, i.e. $e_C(p)=(p_1,p_2)$ in $G_1\times G_2$ and $e_T(p)=(p_1,p_2)$ in $H_1\times H_2$. All subgroups carry the Borel $\sigma$-algebra of their subspace topology and products the product $\sigma$-algebra. Let $\tau$ be a Haar measure on $C$ and $\tau'$ a Haar measure on $T$, coupled in the sense that the image of $\tau'$ under $t\mapsto (y_1,y_2)^{-1}t(y_1,y_2)$ into $H_1\times H_2$ equals the image of $\tau$ under $s\mapsto(\varphi_1\times\varphi_2)(s)$. Then there exist Haar measures $\tau_i$ on $C_i$ and $\tau_i'$ on $T_i$ with $\tau=(e_C)_*(\tau_1\otimes\tau_2)$, $\tau'=(e_T)_*(\tau_1'\otimes\tau_2')$, and, for $i=1,2$, the image of $\tau_i'$ under $t\mapsto y_i^{-1}ty_i$ into $H_i$ equal to the image of $\tau_i$ under $\varphi_i$.
--
--   This is the measure-theoretic half of peeling off one factor in a product of local data: it converts a single coupling between a Haar measure on a centraliser and one on a twisted ($\sigma$-)centraliser over a product group into a pair of factorwise couplings, using that Haar measure on a product of such groups is a product of Haar measures up to a scalar and that push-forward along a product map respects products. It is used by [`AutomorphicForm.semilocal_central_transfer_peel_step`](thm.html#AutomorphicForm.semilocal_central_transfer_peel_step) and [`AutomorphicForm.semilocal_central_transfer_referenceMeasures_peel_step`](thm.html#AutomorphicForm.semilocal_central_transfer_referenceMeasures_peel_step).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_prod_eq_and_coupled_of_coupled_prod.lean

import Mathlib
import Definitions.Def_AutomorphicForm_SigmaCentralizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

theorem AutomorphicForm.exists_prod_eq_and_coupled_of_coupled_prod
    {G₁ G₂ H₁ H₂ : Type}
    [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [SecondCountableTopology G₁] [T2Space G₁]
    [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
    [SecondCountableTopology G₂] [T2Space G₂]
    [Group H₁] [TopologicalSpace H₁] [IsTopologicalGroup H₁] [LocallyCompactSpace H₁]
    [SecondCountableTopology H₁] [T2Space H₁]
    [Group H₂] [TopologicalSpace H₂] [IsTopologicalGroup H₂] [LocallyCompactSpace H₂]
    [SecondCountableTopology H₂] [T2Space H₂]
    (φ₁ : G₁ →* H₁) (hφ₁ : Topology.IsClosedEmbedding φ₁) (φ₂ : G₂ →* H₂) (hφ₂ : Topology.IsClosedEmbedding φ₂)
    (η₁ : H₁ →* H₁) (hη₁ : Continuous η₁) (η₂ : H₂ →* H₂) (hη₂ : Continuous η₂)
    (γ₁ : G₁) (γ₂ : G₂) (δ₁ y₁ : H₁) (δ₂ y₂ : H₂)
    (eC : Subgroup.centralizer ({γ₁} : Set G₁) × Subgroup.centralizer ({γ₂} : Set G₂) →
      Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)))
    (heC : ∀ p, ((eC p : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) : G₁ × G₂) =
      ((p.1 : G₁), (p.2 : G₂)))
    (eT : AutomorphicForm.sigmaCentralizer η₁ δ₁ × AutomorphicForm.sigmaCentralizer η₂ δ₂ →
      AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂))
    (heT : ∀ p, ((eT p : AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) : H₁ × H₂) =
      ((p.1 : H₁), (p.2 : H₂)))
    (τ : @Measure (Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂))) (borel _))
    (hτ : @Measure.IsHaarMeasure _ _ _ (borel _) τ)
    (τ' : @Measure (AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hcpl : @Measure.map _ _ (borel _) (borel (H₁ × H₂))
        (fun t : AutomorphicForm.sigmaCentralizer (η₁.prodMap η₂) (δ₁, δ₂) =>
          (y₁, y₂)⁻¹ * (t : H₁ × H₂) * (y₁, y₂)) τ' =
      @Measure.map _ _ (borel _) (borel (H₁ × H₂))
        (fun s : Subgroup.centralizer ({(γ₁, γ₂)} : Set (G₁ × G₂)) => (φ₁.prodMap φ₂) (s : G₁ × G₂)) τ) :
    ∃ (τ₁ : @Measure (Subgroup.centralizer ({γ₁} : Set G₁)) (borel _))
      (τ₂ : @Measure (Subgroup.centralizer ({γ₂} : Set G₂)) (borel _))
      (τ₁' : @Measure (AutomorphicForm.sigmaCentralizer η₁ δ₁) (borel _))
      (τ₂' : @Measure (AutomorphicForm.sigmaCentralizer η₂ δ₂) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁ ∧ @Measure.IsHaarMeasure _ _ _ (borel _) τ₂ ∧
      @Measure.IsHaarMeasure _ _ _ (borel _) τ₁' ∧ @Measure.IsHaarMeasure _ _ _ (borel _) τ₂' ∧
      τ = @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) eC
            (@Measure.prod _ _ (borel _) (borel _) τ₁ τ₂) ∧
      τ' = @Measure.map _ _ (@Prod.instMeasurableSpace _ _ (borel _) (borel _)) (borel _) eT
            (@Measure.prod _ _ (borel _) (borel _) τ₁' τ₂') ∧
      @Measure.map _ _ (borel _) (borel H₁)
          (fun t : AutomorphicForm.sigmaCentralizer η₁ δ₁ => y₁⁻¹ * (t : H₁) * y₁) τ₁' =
        @Measure.map _ _ (borel _) (borel H₁)
          (fun s : Subgroup.centralizer ({γ₁} : Set G₁) => φ₁ (s : G₁)) τ₁ ∧
      @Measure.map _ _ (borel _) (borel H₂)
          (fun t : AutomorphicForm.sigmaCentralizer η₂ δ₂ => y₂⁻¹ * (t : H₂) * y₂) τ₂' =
        @Measure.map _ _ (borel _) (borel H₂)
          (fun s : Subgroup.centralizer ({γ₂} : Set G₂) => φ₂ (s : G₂)) τ₂ := by sorry
