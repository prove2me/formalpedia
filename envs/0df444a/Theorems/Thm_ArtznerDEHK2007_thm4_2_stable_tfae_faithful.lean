-- Prove2me | Theorems.Thm_ArtznerDEHK2007_thm4_2_stable_tfae_faithful
-- name    : ArtznerDEHK2007.thm4_2_stable_tfae_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T01:34:29.243979+00:00
-- url     : https://prove2.me/theorems/60cc8c49-285d-47da-ab62-072e84f5e070
-- title:
--   Theorem 4.2 as printed (no triviality assumption on $\mathcal F_0$)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P_0)$ be a probability space with a filtration $(\mathcal F_n)_{n\ge 0}$, with no assumption on $\mathcal F_0$, fix a horizon $N$, and let $\mathcal P$ be a closed convex set of test probabilities on $(\Omega,\mathcal F_N)$, absolutely continuous with respect to $\mathbb P_0$, whose subset $\mathcal P^e$ of probabilities equivalent to $\mathbb P_0$ is nonempty. For a bounded adapted process $X$ and a stopping time $\sigma\le N$ let
--
--   $$\Psi_\sigma(X)=\operatorname{ess\,inf}\bigl\{\mathbb E_{\mathbb Q}[X_\tau\mid\mathcal F_\sigma] : \sigma\le\tau\le N \text{ a stopping time},\ \mathbb Q\in\mathcal P^e\bigr\},$$
--
--   and let $\bar\Psi(X)$ be the generalized Snell envelope $\bar\Psi_N(X)=X_N$, $\bar\Psi_n(X)=X_n\wedge\operatorname{ess\,inf}_{\mathbb Q\in\mathcal P^e}\mathbb E_{\mathbb Q}[\bar\Psi_{n+1}(X)\mid\mathcal F_n]$. The following are equivalent:
--
--   1. $\mathcal P$ is stable under pasting (Definition 3.1);
--   2. for every $\mathbb Q\in\mathcal P$ and every value process $X$, $(\Psi_n(X))_{0\le n\le N}$ is a $\mathbb Q$-submartingale;
--   3. for every value process $X$, $\Psi_n(X)=\bar\Psi_n(X)$ a.s. for $0\le n\le N$;
--   4. for every value process $X$ and stopping times $\sigma\le\tau\le N$, $\Psi_\sigma(X)=\Psi_\sigma\bigl(X^{\tau-}+\Psi_\tau({}^\tau X)\mathbf 1_{[\tau,N]}\bigr)$ a.s.
--
--   This is Theorem 4.2 of Artzner, Delbaen, Eber, Heath and Ku as printed, without the assumption that $\mathcal F_0$ is $\mathbb P_0$-trivial that the existing theorem MultiperiodRisk.Bellman.stable_tfae adds. With a non-trivial $\mathcal F_0$ the implications 2–4 $\Rightarrow$ 1 are expected to fail (a four-point example with $N=1$), so this statement is posed as a target for a disproof.
--
--   **Formalization Note** Definitions, encodings and the convention $X_{-1}=0$ are those of the existing theorem; $\mathcal P^e\ne\emptyset$ stands for the paper's convention $\mathbb P_0\in\mathcal P$.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007), doi:10.1007/s10479-006-0132-6; manuscript of Nov. 16, 2004, p. 11, Theorem 4.2

import Mathlib
import Definitions.Def_MultiperiodRisk_Bellman_StopOps

open MeasureTheory MultiperiodRisk.Bellman

theorem ArtznerDEHK2007.thm4_2_stable_tfae_faithful {Ω : Type*} {m : MeasurableSpace Ω} (P₀ : Measure Ω)
    [IsProbabilityMeasure P₀] (ℱ : Filtration ℕ m) (N : ℕ)
    (D : TestSet P₀ ℱ N) (hPe : (Pe D).Nonempty) :
    List.TFAE
      [ IsStable D,
        ∀ f ∈ D.set, ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          Submartingale (fun n => PsiN D X (min n N)) ℱ (Q P₀ f),
        ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          ∀ n ≤ N, PsiN D X n =ᵐ[P₀] PsiBar D X n,
        ∀ X : ℕ → Ω → ℝ, IsValueProcess P₀ ℱ N X →
          ∀ (σ τ : Ω → WithTop ℕ) (hσ : IsBddStoppingTime ℱ N σ)
            (hτ : IsBddStoppingTime ℱ N τ), (∀ ω, σ ω ≤ τ ω) →
            Psi D X σ hσ.1 =ᵐ[P₀] Psi D (bellmanProcess D X τ hτ.1) σ hσ.1 ] := by sorry
