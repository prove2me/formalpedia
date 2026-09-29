-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv
-- name    : AutomorphicForm.exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/dd233363-11ce-5d00-9a1e-472f5b6537fa
-- title:
--   Flow-chart derivatives dominated by words in archimedean derivations
-- statement:
--   Let $K$ be a number field, and let the alphabet of archimedean letters consist of the triples $(w,\,w\text{ real},\,d)$ with $d \in \{H,E,F\}$ together with the triples $(w,\,w\text{ complex},\,d)$ with $d$ among the six directions $H,E,F,iH,iE,iF$. Fix a list $L_0$ of such letters, of length $n$, and a real $\ell>0$. For a word $l$ (a list of letters) and $b : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, write $W\,l\,b$ for the result of applying the invariant derivations of the letters of $l$ to $b$ from right to left, each letter acting by $\varphi \mapsto (g \mapsto \frac{d}{ds}\varphi(g\cdot \mathrm{flow}(s))|_{s=0})$ through `archDerivAt` at a real place and `archDerivAtComplex` at a complex place; write $\mathrm{flow}(d,t)$ for the corresponding one-parameter subgroup, embedded at the place of $d$ via the split torus, upper or lower unipotent matrix (multiplied by $i$ for the letters $iH,iE,iF$), and set $\mathrm{chart}(t) = \prod_{j<n} \mathrm{flow}(L_0[j], t_j)$ in list order, for $t \in \mathbb{R}^n$. The assertion is that there exist a finite set $\Lambda$ of words, each of length $\le n$, and a constant $c \ge 0$, such that for every $b$ with the property that for all words $l$ of length $\le n$ the function $W\,l\,b$ is continuous and satisfies `IsArchSmoothAt` at every real place $w$ (that is, for each $g$ the map $e \mapsto (W\,l\,b)(g\cdot \mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on the set of real $2\times 2$ matrices of nonzero determinant) and `IsArchSmoothAtComplex` at every complex place, and for every $x \in \mathrm{GL}_2(\mathbb{A}_K)$: the function $t \mapsto b(x\cdot\mathrm{chart}(t))$ is $C^n$ on $\mathbb{R}^n$, and for all $k \le n$ and all $t$ with every coordinate in $[-\ell,\ell]$, $\|\,\mathrm{iteratedFDeriv}^k\,(t \mapsto b(x\cdot\mathrm{chart}(t)))\,(t)\| \le c \sum_{l \in \Lambda} \|(W\,l\,b)(x\cdot\mathrm{chart}(t))\|$. In particular $\Lambda$ and $c$ depend only on $K$, $L_0$ and $\ell$, uniformly in $b$ and in the base point $x$.
--
--   This is the classical comparison, in a chart given by a product of one-parameter subgroups, between coordinate partial derivatives of a function on $\mathrm{GL}_2(\mathbb{A}_K)$ and the words in the invariant archimedean derivations applied to it, with constants independent of the function and of the base point. It is used in the passage from $L^p$ bounds on derivatives to pointwise bounds, being cited by [`AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le`](thm.html#AutomorphicForm.exists_isCompact_forall_norm_le_mul_of_forall_eLpNorm_foldr_archDeriv_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv.lean

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

theorem AutomorphicForm.exists_forall_contDiff_norm_iteratedFDeriv_comp_flowChart_le_sum_foldr_archDeriv
    (K : Type) [Field K] [NumberField K]
    (L₀ : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))
    (ℓ : ℝ) (hℓ : 0 < ℓ) :
    let W : List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) →
        (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun l b => l.foldr (fun d φ => Sum.elim (fun d => archDerivAt d.2.1 d.2.2 φ)
        (fun d => archDerivAtComplex d.2.1 d.2.2 φ) d) b
    let flow : ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)) → ℝ → AdelicGL2 (𝓞 K) K :=
      fun d t => Sum.elim (fun d => archFlowAt d.2.1 d.2.2 t) (fun d => archFlowAtComplex d.2.1 d.2.2 t) d
    let chart : (Fin L₀.length → ℝ) → AdelicGL2 (𝓞 K) K :=
      fun t => (List.ofFn fun j => flow (L₀.get j) (t j)).prod
    ∃ (Λ : Finset (List ((Σ' w : InfinitePlace K, Σ' _ : w.IsReal, ArchDir) ⊕
          (Σ' w : InfinitePlace K, Σ' _ : w.IsComplex, ArchDirComplex)))) (c : ℝ),
      (∀ l ∈ Λ, l.length ≤ L₀.length) ∧ 0 ≤ c ∧
      ∀ b : AdelicGL2 (𝓞 K) K → ℂ,
        (∀ l, l.length ≤ L₀.length →
          Continuous (W l b) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsReal), IsArchSmoothAt hw (W l b)) ∧
          (∀ (w : InfinitePlace K) (hw : w.IsComplex), IsArchSmoothAtComplex hw (W l b))) →
        ∀ x : AdelicGL2 (𝓞 K) K,
          ContDiff ℝ L₀.length (fun t : Fin L₀.length → ℝ => b (x * chart t)) ∧
          ∀ k : ℕ, k ≤ L₀.length → ∀ t : Fin L₀.length → ℝ, (∀ j, t j ∈ Set.Icc (-ℓ) ℓ) →
            ‖iteratedFDeriv ℝ k (fun t : Fin L₀.length → ℝ => b (x * chart t)) t‖ ≤
              c * ∑ l ∈ Λ, ‖W l b (x * chart t)‖ := by sorry
