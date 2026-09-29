-- Prove2me | Theorems.Thm_AutomorphicForm_areMatchingLocal_heckeWord_sum_coeff_univWord_mul_heckeWord_of_ramificationIdx_eq_one_of_prime
-- name    : AutomorphicForm.areMatchingLocal_heckeWord_sum_coeff_univWord_mul_heckeWord_of_ramificationIdx_eq_one_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/99f915e8-4fca-5547-9039-06fe04d5d7f8
-- title:
--   Matching of the Hecke word T_w^k z_w^j under prime-degree base change
-- statement:
--   Let $K \subseteq L$ be number fields with $[L:K]$ prime, let $\sigma$ be a $K$-automorphism of $L$ with $\sigma \neq 1$, and let $v$ be a height-one prime of $\mathcal O_K$ all of whose extensions $w'$ to $\mathcal O_L$ satisfy $e(w'/v)=1$ in the sense of `Ideal.ramificationIdx'`. Fix one such extension $w$, an irreducible element $\varpi$ of the valuation ring of the completion $L_w$ whose image in $L_w$ is non-zero, and, for $U_w$ the image of $\mathrm{GL}_2(\mathcal O_w)$ in $\mathrm{GL}_2(L_w)$ and $g_w = \mathrm{diag}(\varpi,1)$, a family $rT : \mathrm{Fin}\,n \to \mathrm{GL}_2(L_w)$ forming a Hecke coset system: each $rT(i)$ lies in $U_w g_w U_w$, every element of that double coset lies in some $rT(i)U_w$, and the cosets $rT(i)U_w$ are pairwise distinct. Let $z \in \mathrm{GL}_2(L_w)$ have matrix $\varpi \cdot 1$. Fix likewise $\varpi_K$, a Hecke coset system $rK : \mathrm{Fin}\,n_K \to \mathrm{GL}_2(K_v)$ for $U_v\,\mathrm{diag}(\varpi_K,1)\,U_v$ with $U_v$ the image of $\mathrm{GL}_2(\mathcal O_v)$, and $z_K$ with matrix $\varpi_K \cdot 1$. Then, for all $k, j \in \mathbb N$, the predicate `AreMatchingLocal K L v σ` (that is, `AreMatchingOn` for $\sigma$ relative to the Haar measures `semiLocalHaar K L v` and `localHaar K v`, the latter normalised by the compact open subgroup of integral units) holds for the following pair of functions. On $\mathrm{GL}_2(L \otimes_K K_v)$: the function sending $x$ to $\sum_{\iota : \mathrm{Fin}\,k \to \mathrm{Fin}\,n} \mathbf 1\big[(\gamma_\iota)^{-1}x \in \mathrm{semiLocalIntegralSet}\big]$, where $\gamma_\iota$ is the image in $\mathrm{GL}_2(L \otimes_K K_v)$, under `semiLocalComponent` composed with the embedding [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of $\mathrm{GL}_2(L_w)$ into $\mathrm{GL}_2$ of the finite adeles of $L$ (identity at the other places), of $rT(\iota(0)) \cdots rT(\iota(k-1)) \, z^{j}$, and `semiLocalIntegralSet` consists of those $g$ with both $g$ and $g^{-1}$ having entries in the semi-local integers. On $\mathrm{GL}_2(K_v)$: the function sending $x$ to
--   $$\sum_{r} c_r \, \frac{N(v)^{r(1)}}{N(w)^{j}} \sum_{\iota : \mathrm{Fin}\,r(0) \to \mathrm{Fin}\,n_K} \mathbf 1\big[(rK(\iota(0)) \cdots rK(\iota(r(0)-1)) \, z_K^{\,r(1)})^{-1}x \in \mathrm{localIntegralSet}\big],$$
--   the sum being over the support of the two-variable polynomial $\mathrm{univWord}(f-1,k,j) = P_f(X_0,X_1)^k \cdot (X_1^{f})^{j} \in \mathbb C[X_0,X_1]$ with $c_r$ its coefficients, $f = \mathrm{inertiaDeg'}(v,w)$, and $P_m$ given by $P_0 = 2$, $P_1 = s$, $P_{m+2} = s P_{m+1} - e P_m$; here $N$ denotes `Ideal.absNorm` and `localIntegralSet` consists of those $g \in \mathrm{GL}_2(K_v)$ with $g$ and $g^{-1}$ integral.
--
--   This is the fundamental lemma for the spherical Hecke algebra of $\mathrm{GL}_2$ in cyclic base change of prime degree, made explicit on the Hecke word $T_w^k z_w^j$ at a place unramified in $L/K$: the local component of the transferred test function is written out as a universal $\mathbb C$-linear combination of words $T_v^{a} z_v^{c}$ with coefficients read off from the polynomial `univWord`. It feeds the global matching of test functions used in the comparison of twisted and ordinary trace formulae, and is cited by the statements that assemble matching data place by place and by the subsequent Satake–Laurent identities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_areMatchingLocal_heckeWord_sum_coeff_univWord_mul_heckeWord_of_ramificationIdx_eq_one_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.areMatchingLocal_heckeWord_sum_coeff_univWord_mul_heckeWord_of_ramificationIdx_eq_one_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1)
    (w : v.Extension (𝓞 L))
    (ϖ : w.1.adicCompletionIntegers L) (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ ≠ 0)
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L))
      (LocalGL2.diagPi ϖ hϖ0) rT)
    (z : GL (Fin 2) (w.1.adicCompletion L))
    (hz : (z : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)) =
      algebraMap (w.1.adicCompletionIntegers L) (w.1.adicCompletion L) ϖ •
        (1 : Matrix (Fin 2) (Fin 2) (w.1.adicCompletion L)))
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
    (k j : ℕ) :
    AreMatchingLocal K L v σ
      (fun x : GL (Fin 2) (L ⊗[K] v.adicCompletion K) =>
        ∑ ι : Fin k → Fin n,
          (semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))
            ((semiLocalComponent K L v (AdelicDock.localEmbed (𝓞 L) L w.1
              ((List.ofFn fun m => rT (ι m)).prod * z ^ j)))⁻¹ * x))
      (fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ r ∈ (SatakeCombination.univWord (v.asIdeal.inertiaDeg' w.1.asIdeal - 1) k j).support,
          (SatakeCombination.univWord (v.asIdeal.inertiaDeg' w.1.asIdeal - 1) k j).coeff r *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (r 1) / (Ideal.absNorm w.1.asIdeal : ℂ) ^ j *
            ∑ ι : Fin (r 0) → Fin nK,
              (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
                (((List.ofFn fun m => rK (ι m)).prod * zK ^ (r 1))⁻¹ * x)) := by sorry
