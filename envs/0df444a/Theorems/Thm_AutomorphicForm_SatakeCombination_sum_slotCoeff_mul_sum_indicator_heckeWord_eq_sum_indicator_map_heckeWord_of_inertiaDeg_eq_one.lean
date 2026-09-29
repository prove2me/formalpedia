-- Prove2me | Theorems.Thm_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one
-- name    : AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/20f46916-de80-51f3-aec3-2da8ecd780be
-- title:
--   Satake word comparison at an inertia-degree-one place
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and let $v$ be a height-one prime of $\mathcal O_K$. Let $ws$ assign to every height-one prime $u$ of $\mathcal O_K$ a prime $ws(u)$ of $\mathcal O_L$ lying under $u$, and assume the inertia degree of $ws(v)$ over $v$ is $1$. On the $L$-side fix an irreducible $\varpi$ in the valuation ring of $L_{ws(v)}$ whose image in $L_{ws(v)}$ is nonzero, a natural number $n$ and $rL : \mathrm{Fin}\,n \to \mathrm{GL}_2(L_{ws(v)})$ forming a Hecke coset system for the subgroup $\mathrm{GL}_2$ of integral matrices (the range of the map induced by the structure map) and the element $\mathrm{diag}(\varpi,1)$, i.e. each $rL\,i$ lies in the double coset, every element of the double coset has the same left coset as some $rL\,i$, and these left cosets are pairwise distinct; and let $z$ be the unit with matrix $\varpi\cdot 1$. Fix the analogous data $\varpi_K$, $n_K$, $rK$, $z_K$ over $K_v$, natural numbers $k,j$, and a ring isomorphism $e : L_{ws(v)} \simeq K_v$ with $\mathrm{v}(e\,x) = \mathrm{v}(x)$ for all $x$. Then, as functions of $x \in \mathrm{GL}_2(K_v)$, $$\sum_{r \in \mathrm{supp}} \mathrm{slotCoeff}(r)\sum_{\iota : \mathrm{Fin}(r_0)\to\mathrm{Fin}\,n_K} \mathbf 1\big((rK(\iota_0)\cdots rK(\iota_{r_0-1})\,z_K^{\,r_1})^{-1}x\big) = \sum_{\iota : \mathrm{Fin}\,k\to\mathrm{Fin}\,n} \mathbf 1\big(e_*(rL(\iota_0)\cdots rL(\iota_{k-1})\,z^{\,j})^{-1}x\big),$$ where $\mathbf 1$ is the complex indicator of the set of $g \in \mathrm{GL}_2(K_v)$ with both $g$ and $g^{-1}$ having entries in the valuation ring, the sum on the left runs over the support of the polynomial `slotWord K L ws v k j` $= \mathrm{satakePow}(\mathrm{slotDeg})(X_0,X_1)^k\cdot (X_1^{\mathrm{slotDeg}})^j$ with $\mathrm{slotDeg}$ the inertia degree of $ws(v)$ over $v$, $\mathrm{slotCoeff}(r)$ is the coefficient of this polynomial at $r$ multiplied by $N(v)^{r_1}/N(ws(v))^{j}$, and $e_*$ denotes the induced map on $\mathrm{GL}_2$.
--
--   This is the split (inertia degree one) case of the comparison between the base-change Satake combination of Hecke words over $K$ and the single word $T_w^k z_w^j$ over $L$, transported along a valuation-preserving identification of the two completions. It feeds the weighted Hecke-word identity [`AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one`](thm.html#AutomorphicForm.twistedWeighted_eq_finrank_mul_weighted_heckeWord_of_inertiaDeg_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SatakeCombination_sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.SatakeCombination.sum_slotCoeff_mul_sum_indicator_heckeWord_eq_sum_indicator_map_heckeWord_of_inertiaDeg_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K))

    (ws : ∀ u : HeightOneSpectrum (𝓞 K), u.Extension (𝓞 L))
    (hsplit : v.asIdeal.inertiaDeg' (ws v).1.asIdeal = 1)
    (ϖ : (ws v).1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rL : Fin n → GL (Fin 2) ((ws v).1.adicCompletion L))
    (hrL : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rL)
    (z : GL (Fin 2) ((ws v).1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)) =
      algebraMap ((ws v).1.adicCompletionIntegers L) ((ws v).1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) ((ws v).1.adicCompletion L)))

    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (hϖK0 : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK ≠ 0)
    (nK : ℕ) (rK : Fin nK → GL (Fin 2) (v.adicCompletion K))
    (hrK : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
      (LocalGL2.diagPi ϖK hϖK0) rK)
    (zK : GL (Fin 2) (v.adicCompletion K))
    (hzK : (zK : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖK •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (k j : ℕ)

    (e : (ws v).1.adicCompletion L ≃+* v.adicCompletion K)
    (he : ∀ x : (ws v).1.adicCompletion L, Valued.v (e x) = Valued.v x) :
    (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.slotWord K L ws v k j).support,
          SatakeCombination.slotCoeff K L ws v k j r *
            ∑ ι : Fin (r 0) → Fin nK,
              (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (r 1))⁻¹ * x)) =
      fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (AutomorphicForm.localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            ((Matrix.GeneralLinearGroup.map e.toRingHom ((List.ofFn fun m => rL (ι m)).prod * z ^ j))⁻¹ * x) := by sorry
