-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq
-- name    : AutomorphicForm.exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/1af689f0-8b99-5ce6-ad53-eccce6089015
-- title:
--   Haar comparison for flow-chart boxes in GL₂(A_K)
-- statement:
--   Let $K$ be a number field and $N \neq 0$ an ideal of $\mathcal{O}_K$. Let $L_0$ be a repetition-free list, containing every element, of the index set whose members are pairs (real place $w$, direction in $\{H,E,F^-\}$) together with pairs (complex place $w$, direction in $\{H,E,F^-,iH,iE,iF^-\}$). The statement introduces $\mathrm{flow}$, sending such an index and $t \in \mathbb{R}$ to the element of $\mathrm{GL}_2(\mathbb{A}_K)$ obtained by placing at $w$ the split-torus, upper- or lower-unipotent matrix with parameter $t$ (respectively $ti$ in the imaginary complex directions), and the chart $\mathrm{chart}(t) = \prod_j \mathrm{flow}(L_0[j], t_j)$, the product taken in list order, with $t$ ranging over $\mathbb{R}^{|L_0|}$. The assertion: there exist $\ell > 0$, a compact $\Theta \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ and $c \in \mathbb{R}_{\geq 0}$ such that for every $x \in \mathrm{GL}_2(\mathbb{A}_K)$, every $\kappa \in [0,\infty]$ and every measurable $G : \mathrm{GL}_2(\mathbb{A}_K) \to [0,\infty]$ which is right invariant under the intersection of `principalLevel` at $N$ with the kernel of the archimedean projection `glArch`, and which satisfies $\kappa\, G(y) \le G(y\,\sigma_w(\mathrm{diag}(t,t)))$ for all $y$, all real $w$ and all $t \in \mathbb{R}^\times$ with $t \in [1/2,2]$, and likewise $\kappa\, G(y) \le G(y\,\sigma_w(\mathrm{diag}(z,z)))$ for all complex $w$ and $z \in \mathbb{C}^\times$ with $\|z-1\| \le 1/2$ (where $\sigma_w$ denotes the inclusion at $w$), one has
--   $$\kappa^{\,r}\int_{[-\ell,\ell]^{|L_0|}} G(x\,\mathrm{chart}(t))\,dt \;\le\; c\int_{x\Theta} G \,d\mu,$$
--   with $r$ the number of infinite places of $K$, the left integral a lower Lebesgue integral over the box in $\mathbb{R}^{|L_0|}$, and $\mu =$ `adelicGLHaar` the Haar measure on $\mathrm{GL}_2(\mathbb{A}_K)$ for its Borel structure.
--
--   This is the Haar-measure comparison in archimedean flow coordinates: a box integral of a right-level-invariant function along the chart built from the one-parameter flows at the infinite places is dominated, up to a constant and up to the central collar factor $\kappa^{r}$, by a Haar integral over a compact translate. It is used in the passage from integral bounds on archimedean derivatives to pointwise bounds on compacta, namely by [`AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le`](thm.html#AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq.lean

import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.InfinitePlace
open AutomorphicForm
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_lintegral_comp_flowChart_le_mul_lintegral_of_forall_mul_eq
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (hL₀ : L₀.Nodup) (hL₀' : ∀ d, d ∈ L₀) :
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun j => flow (L₀.get j) (t j)).prod
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ Θ : Set (AdelicGL2 (𝓞 K) K), IsCompact Θ ∧ ∃ c : NNReal,
      ∀ (x : AdelicGL2 (𝓞 K) K) (κ : ENNReal) (G : AdelicGL2 (𝓞 K) K → ENNReal), Measurable G →
        (∀ y : AdelicGL2 (𝓞 K) K, ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, G (y * u) = G y) →
        (∀ (y : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) (hw : w.IsReal) (t : ℝˣ), (t : ℝ) ∈ Set.Icc (1 / 2) 2 →
          κ * G y ≤ G (y * archRealGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℝ →+* Matrix (Fin 2) (Fin 2) ℝ).toMonoidHom t))) →
        (∀ (y : AdelicGL2 (𝓞 K) K) (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂˣ), ‖(z : ℂ) - 1‖ ≤ 1 / 2 →
          κ * G y ≤ G (y * archComplexGLAt hw (Units.map (Matrix.scalar (Fin 2) : ℂ →+* Matrix (Fin 2) (Fin 2) ℂ).toMonoidHom z))) →
        κ ^ Fintype.card (InfinitePlace K) *
            ∫⁻ t in Set.pi Set.univ (fun _ : Fin L₀.length => Set.Icc (-ℓ) ℓ), G (x * chart t) ≤
          (c : ENNReal) * ∫⁻ y in (fun θ => x * θ) '' Θ, G y ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
